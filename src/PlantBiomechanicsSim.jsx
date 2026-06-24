import { useState, useRef, useCallback, useEffect, useMemo } from "react";

function dist(a, b) { return Math.sqrt((a.x-b.x)**2+(a.y-b.y)**2); }
function computeCentroid(verts) {
  let cx=0,cy=0; for(let i=0; i<verts.length; i++){cx+=verts[i].x;cy+=verts[i].y;}
  return {x:cx/verts.length,y:cy/verts.length};
}
function pointInPolygon(px,py,poly) {
  let inside=false;
  for(let i=0,j=poly.length-1;i<poly.length;j=i++){
    const xi=poly[i].x,yi=poly[i].y,xj=poly[j].x,yj=poly[j].y;
    if((yi>py)!==(yj>py)&&px<((xj-xi)*(py-yi))/(yj-yi)+xi) inside=!inside;
  }
  return inside;
}
function circumcircle(p1,p2,p3) {
  const ax=p1.x,ay=p1.y,bx=p2.x,by=p2.y,cx=p3.x,cy=p3.y;
  const D=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by));
  if(Math.abs(D)<1e-10) return {x:0,y:0,r:Infinity};
  const ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/D;
  const uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/D;
  return {x:ux,y:uy,r:Math.sqrt((ax-ux)**2+(ay-uy)**2)};
}
function delaunayTriangulate(points) {
  let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity;
  for(const p of points){if(p.x<minX)minX=p.x;if(p.y<minY)minY=p.y;if(p.x>maxX)maxX=p.x;if(p.y>maxY)maxY=p.y;}
  const dx=maxX-minX,dy=maxY-minY,dmax=Math.max(dx,dy)*2;
  const st0={x:minX-dmax,y:minY-dmax},st1={x:minX+dmax*3,y:minY-dmax},st2={x:minX,y:minY+dmax*3};
  const allPts=[st0,st1,st2,...points];
  let triangles=[{a:0,b:1,c:2}];
  for(let pi=3;pi<allPts.length;pi++){
    const p=allPts[pi],bad=[];
    for(let ti=0;ti<triangles.length;ti++){
      const t=triangles[ti],cc=circumcircle(allPts[t.a],allPts[t.b],allPts[t.c]);
      if((p.x-cc.x)**2+(p.y-cc.y)**2<cc.r*cc.r+1e-6) bad.push(ti);
    }
    const edgeCount={},ek=(a,b)=>a<b?`${a}-${b}`:`${b}-${a}`;
    for(const ti of bad){const t=triangles[ti];for(const [ea,eb] of [[t.a,t.b],[t.b,t.c],[t.c,t.a]]){const k=ek(ea,eb);edgeCount[k]=(edgeCount[k]||0)+1;}}
    const polygon=[];
    for(const ti of bad){const t=triangles[ti];for(const [ea,eb] of [[t.a,t.b],[t.b,t.c],[t.c,t.a]]){if(edgeCount[ek(ea,eb)]===1)polygon.push([ea,eb]);}}
    const badSet=new Set(bad);
    triangles=triangles.filter((_,i)=>!badSet.has(i));
    for(const [ea,eb] of polygon) triangles.push({a:ea,b:eb,c:pi});
  }
  triangles=triangles.filter(t=>t.a>=3&&t.b>=3&&t.c>=3);
  return triangles.map(t=>({a:t.a-3,b:t.b-3,c:t.c-3}));
}
function subdivideBoundary(pts, maxEdgeLen) {
  const out=[];
  for(let i=0;i<pts.length;i++){
    const a=pts[i],b=pts[(i+1)%pts.length],d=dist(a,b),n=Math.max(1,Math.ceil(d/maxEdgeLen));
    out.push(a);
    for(let k=1;k<n;k++) out.push({x:a.x+(b.x-a.x)*k/n,y:a.y+(b.y-a.y)*k/n});
  }
  return out;
}
function generateInteriorPoints(boundary, spacing=22) {
  let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity;
  for(const p of boundary){if(p.x<minX)minX=p.x;if(p.y<minY)minY=p.y;if(p.x>maxX)maxX=p.x;if(p.y>maxY)maxY=p.y;}
  const pts=[],margin=spacing*0.5;
  for(let y=minY+margin;y<maxY-margin+1;y+=spacing){
    for(let x=minX+margin;x<maxX-margin+1;x+=spacing){
      const ox=((Math.round((y-minY)/spacing))%2)*spacing*0.5,px=x+ox;
      if(pointInPolygon(px,y,boundary)){
        let tooClose=false;
        for(let i=0; i<boundary.length; i++){if(dist({x:px,y},boundary[i])<spacing*0.45){tooClose=true;break;}}
        if(!tooClose) pts.push({x:px,y});
      }
    }
  }
  return pts;
}
function buildMesh(boundaryPts, subdivisionMaxEdge=0) {
  const tolerance = 1e-3;
  boundaryPts = boundaryPts.filter((p, idx) => {
    if (idx === 0) return true;
    return dist(p, boundaryPts[idx - 1]) > tolerance;
    });
   // Also check the closing edge between the last and first points
   if (boundaryPts.length > 1 && dist(boundaryPts[boundaryPts.length - 1], boundaryPts[0]) <= tolerance) {
    boundaryPts.pop();
  }
  if(subdivisionMaxEdge>0) boundaryPts=subdivideBoundary(boundaryPts,subdivisionMaxEdge);
  const nBoundary=boundaryPts.length;
  const interiorSpacing=subdivisionMaxEdge>0?subdivisionMaxEdge*1.1:22;
  const interior=generateInteriorPoints(boundaryPts,interiorSpacing);
  const allPts=[...boundaryPts,...interior];
  const verts=allPts.map((p,i)=>({x:p.x,y:p.y,vx:0,vy:0,pinned:false,isBoundary:i<nBoundary}));
  const triangles=delaunayTriangulate(allPts);
  
  const goodTris=triangles.filter(t=>{
    const boundaryVerticesCount = (t.a < nBoundary ? 1 : 0) + (t.b < nBoundary ? 1 : 0) + (t.c < nBoundary ? 1 : 0);
    if (boundaryVerticesCount > 0 && boundaryVerticesCount < 3) return true;
    const cx=(allPts[t.a].x+allPts[t.b].x+allPts[t.c].x)/3;
    const cy=(allPts[t.a].y+allPts[t.b].y+allPts[t.c].y)/3;
    return pointInPolygon(cx,cy,boundaryPts);
  });

  const edgeSet=new Set(),ek=(a,b)=>a<b?`${a}-${b}`:`${b}-${a}`,edges=[];
  const boundaryEdgeKeys=new Set();
  for(let i=0;i<nBoundary;i++) boundaryEdgeKeys.add(ek(i,(i+1)%nBoundary));
  const isBoundaryEdge=(a,b)=>a<nBoundary&&b<nBoundary&&boundaryEdgeKeys.has(ek(a,b));
  for(let i=0; i<goodTris.length; i++){
    const t=goodTris[i];
    for(const [a,b] of [[t.a,t.b],[t.b,t.c],[t.c,t.a]]){
      const k=ek(a,b);
      if(!edgeSet.has(k)){
        edgeSet.add(k);
        edges.push({i:a,j:b,stiffness:1.0,restLength:dist(allPts[a],allPts[b]),
          isBoundary:isBoundaryEdge(a,b),aniso:{angle:0,ratio:1.0}});
      }
    }
  }
  for(let i=0;i<nBoundary;i++){
    const j=(i+1)%nBoundary,k=ek(i,j);
    if(!edgeSet.has(k)){
      edgeSet.add(k);
      edges.push({i,j,stiffness:1.0,restLength:dist(allPts[i],allPts[j]),
        isBoundary:true,aniso:{angle:0,ratio:1.0}});
    }
  }
  return {vertices:verts,edges,triangles:goodTris,nBoundary};
}

function effectiveStiffness(edge, ax, ay) {
  const {stiffness, aniso} = edge;
  if(!aniso || aniso.ratio===1.0) return stiffness;
  const {angle, ratio} = aniso;
  const edLen = Math.sqrt(ax*ax+ay*ay)||1;
  const ex=ax/edLen, ey=ay/edLen;
  const px=Math.cos(angle), py=Math.sin(angle);
  const dot=ex*px+ey*py;
  const cos2=dot*dot;
  return stiffness*(cos2 + ratio*(1-cos2));
}

// Zero-allocation function. Mutates 'forces' in-place.
function computeNetForces(verts, edges, boundaryEdgeIndices, pressure, externalForces, forces) {
  const n = verts.length;
  for (let i = 0; i < n; i++) {
    forces[i].x = 0; forces[i].y = 0;
  }

  for (let k = 0; k < edges.length; k++) {
    const edge = edges[k];
    const a = verts[edge.i], b = verts[edge.j];
    const dx = b.x - a.x, dy = b.y - a.y;
    const d = Math.sqrt(dx * dx + dy * dy) || 0.001;
    const eff = effectiveStiffness(edge, dx, dy);
    const strain = (d - edge.restLength) / (edge.restLength || 0.001);
    const fm = eff * strain * d;
    const fx = (fm * dx) / d, fy = (fm * dy) / d;
    forces[edge.i].x += fx; forces[edge.i].y += fy;
    forces[edge.j].x -= fx; forces[edge.j].y -= fy;
  }

  if (Math.abs(pressure) > 0.001) {
    let bVertsCount = 0, cx = 0, cy = 0;
    for (let i = 0; i < n; i++) {
      if (verts[i].isBoundary) { cx += verts[i].x; cy += verts[i].y; bVertsCount++; }
    }
    if (bVertsCount > 0) { cx /= bVertsCount; cy /= bVertsCount; }
    else {
      for(let i = 0; i < n; i++) { cx += verts[i].x; cy += verts[i].y; }
      cx /= n; cy /= n;
    }

    for (let k = 0; k < boundaryEdgeIndices.length; k++) {
      const edge = edges[boundaryEdgeIndices[k]];
      const a = verts[edge.i], b = verts[edge.j];
      const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
      const edx = b.x - a.x, edy = b.y - a.y;
      const len = Math.sqrt(edx * edx + edy * edy) || 0.001;
      let nx = -edy / len, ny = edx / len;
      if (nx * (cx - mx) + ny * (cy - my) > 0) { nx = -nx; ny = -ny; }
      const pf = pressure * len * 0.5;
      forces[edge.i].x += nx * pf; forces[edge.i].y += ny * pf;
      forces[edge.j].x += nx * pf; forces[edge.j].y += ny * pf;
    }
  }

  for (let k = 0; k < externalForces.length; k++) {
    const ef = externalForces[k];
    if (ef.vertexIndex < n) {
      forces[ef.vertexIndex].x += ef.fx;
      forces[ef.vertexIndex].y += ef.fy;
    }
  }

  for (let i = 0; i < n; i++) {
    if (verts[i].pinned) { forces[i].x = 0; forces[i].y = 0; }
  }
}

// Zero-allocation inner loop physics solver
function simulateStep(vertices, edges, boundaryEdgeIndices, pressure, externalForces, cgState, alpha = 0.04) {
  const verts = vertices.map(v => ({ ...v })); // Clone once per frame
  const n = verts.length;

  if (!cgState.prevForces || cgState.prevForces.length !== n) {
    cgState.prevForces = Array.from({ length: n }, () => ({ x: 0, y: 0 }));
    cgState.searchDirections = Array.from({ length: n }, () => ({ x: 0, y: 0 }));
    cgState.currentForces = Array.from({ length: n }, () => ({ x: 0, y: 0 }));
    cgState.isFirstStep = true;
  }

  const cgIterations = 2;

  for (let iter = 0; iter < cgIterations; iter++) {
    computeNetForces(verts, edges, boundaryEdgeIndices, pressure, externalForces, cgState.currentForces);

    let dotNew = 0;
    let dotOld = 0;

    for (let i = 0; i < n; i++) {
      if (verts[i].pinned) continue;
      dotNew += cgState.currentForces[i].x * cgState.currentForces[i].x + cgState.currentForces[i].y * cgState.currentForces[i].y;
      dotOld += cgState.prevForces[i].x * cgState.prevForces[i].x + cgState.prevForces[i].y * cgState.prevForces[i].y;
    }

    let beta = 0;
    if (!cgState.isFirstStep && dotOld > 1e-10) {
      beta = dotNew / dotOld;
      if (beta > 1.5 || beta < 0) beta = 0;
    }

    for (let i = 0; i < n; i++) {
      if (verts[i].pinned) {
        cgState.searchDirections[i].x = 0;
        cgState.searchDirections[i].y = 0;
        continue;
      }
      cgState.searchDirections[i].x = cgState.currentForces[i].x + beta * cgState.searchDirections[i].x;
      cgState.searchDirections[i].y = cgState.currentForces[i].y + beta * cgState.searchDirections[i].y;

      verts[i].x += cgState.searchDirections[i].x * alpha;
      verts[i].y += cgState.searchDirections[i].y * alpha;

      cgState.prevForces[i].x = cgState.currentForces[i].x;
      cgState.prevForces[i].y = cgState.currentForces[i].y;
    }

    cgState.isFirstStep = false;
  }

  let sumSq = 0, cnt = 0;
  for (let i = 0; i < n; i++) {
    if (verts[i].pinned) continue;
    sumSq += cgState.currentForces[i].x ** 2 + cgState.currentForces[i].y ** 2; cnt++;
  }
  const forceNorm = cnt > 0 ? Math.sqrt(sumSq / cnt) : 0;

  return { verts, forceNorm };
}

function computeEdgeStress(vertices,edges,restVertices) {
  return edges.map(ed=>{
    const a=vertices[ed.i],b=vertices[ed.j],ra=restVertices[ed.i],rb=restVertices[ed.j];
    if(!a||!b||!ra||!rb) return 0;
    return Math.abs((dist(a,b)-dist(ra,rb))/(dist(ra,rb)||0.001))*ed.stiffness;
  });
}
function computeVertexDisplacement(vertices,restVertices) {
  return vertices.map((v,i)=>{
    const r=restVertices[i]; if(!r) return 0;
    return Math.sqrt((v.x-r.x)**2+(v.y-r.y)**2);
  });
}
function stressColor(t) {
  if(t<0.5){const s=t*2;return `rgb(${Math.round(30+180*s)},${Math.round(80+120*s)},${Math.round(200-180*s)})`;}
  const s=(t-0.5)*2;return `rgb(${Math.round(210+45*s)},${Math.round(200-180*s)},${Math.round(20)})`;
}
function dispColor(t) {
  return `rgb(${Math.round(20+220*t)},${Math.round(150-130*t)},${Math.round(180+75*t)})`;
}
function buildDisplacementArrows(vertices,restVertices,spacing=45) {
  const arrows=[],cells={};
  for(let i=0; i<vertices.length; i++){
    const v=vertices[i], r=restVertices[i]; if(!r) continue;
    const cx=Math.round(v.x/spacing),cy=Math.round(v.y/spacing),k=`${cx},${cy}`;
    if(!cells[k]) cells[k]={sumDx:0,sumDy:0,sumX:0,sumY:0,n:0};
    cells[k].sumDx+=v.x-r.x; cells[k].sumDy+=v.y-r.y;
    cells[k].sumX+=v.x; cells[k].sumY+=v.y; cells[k].n++;
  }
  for(const c of Object.values(cells)){
    const n=c.n,dx=c.sumDx/n,dy=c.sumDy/n,mag=Math.sqrt(dx*dx+dy*dy);
    if(mag<0.5) continue;
    arrows.push({x:c.sumX/n,y:c.sumY/n,dx,dy,mag});
  }
  return arrows;
}

const makeRect=(cx,cy,w,h)=>[{x:cx-w/2,y:cy-h/2},{x:cx+w/2,y:cy-h/2},{x:cx+w/2,y:cy+h/2},{x:cx-w/2,y:cy+h/2}];
const makeStrip=(cx,cy,w,h,nSeg=14)=>{
  const pts=[];
  for(let i=0;i<=nSeg;i++) pts.push({x:cx-w/2+(w*i)/nSeg,y:cy-h/2});
  pts.push({x:cx+w/2,y:cy});
  for(let i=nSeg;i>=0;i--) pts.push({x:cx-w/2+(w*i)/nSeg,y:cy+h/2});
  pts.push({x:cx-w/2,y:cy}); return pts;
};
const makeHex=(cx,cy,r)=>Array.from({length:6},(_,i)=>{const a=(Math.PI/3)*i-Math.PI/2;return{x:cx+r*Math.cos(a),y:cy+r*Math.sin(a)};});
const makeCircle=(cx,cy,r,n=20)=>Array.from({length:n},(_,i)=>{const a=(2*Math.PI*i)/n-Math.PI/2;return{x:cx+r*Math.cos(a),y:cy+r*Math.sin(a)};});
const makeLeaf=(cx,cy,len)=>Array.from({length:16},(_,i)=>{const t=(i/16)*2*Math.PI,r=len*0.5*(1+0.4*Math.cos(2*t))*(1+0.2*Math.cos(t));return{x:cx+r*Math.cos(t),y:cy+r*Math.sin(t)*0.6};});

const VIRIDIS=[[68,1,84],[72,20,103],[79,42,122],[82,62,135],[80,82,144],[72,101,148],[62,120,150],[53,138,149],[45,155,143],[41,172,130],[53,187,111],[79,199,87],[119,209,60],[165,218,33],[214,225,17],[253,231,37]];
function viridis(t){
  const s=Math.max(0,Math.min(1,t)),i=s*(VIRIDIS.length-2),lo=Math.floor(i),f=i-lo;
  const a=VIRIDIS[lo],b=VIRIDIS[lo+1];
  return [Math.round(a[0]+(b[0]-a[0])*f),Math.round(a[1]+(b[1]-a[1])*f),Math.round(a[2]+(b[2]-a[2])*f)];
}
function stiffnessEdgeColor(s,isBoundary){
  const [r,g,b]=viridis(Math.min(s/3,1));
  return `rgba(${r},${g},${b},${isBoundary?1:0.6})`;
}
function stiffnessLabelColor(s){const [r,g,b]=viridis(Math.min(s/3,1));return `rgb(${r},${g},${b})`;}
function triFillColor(edges,tri){
  const s1=tri.ea!=null?edges[tri.ea]?.stiffness??1:1,s2=tri.eb!=null?edges[tri.eb]?.stiffness??1:1,s3=tri.ec!=null?edges[tri.ec]?.stiffness??1:1;
  const avg=(s1+s2+s3)/3,t=Math.min(avg/3,1);
  return `rgba(${Math.round(35+70*(1-t))},${Math.round(70+70*t)},${Math.round(25+35*(1-t))},0.4)`;
}

function anisoColor(angle, ratio) {
  //const hue = ((angle % Math.PI) / Math.PI * 360 + 360) % 360;
 // const sat = Math.round(Math.min(Math.abs(1 - ratio) / 2, 1) * 90);
  //const lig = 45;
  const [r,g,b]=viridis(Math.min(1-ratio,1))
return `rgba(${r},${g},${b},${0.6})`;

}

const CANVAS_W=700,CANVAS_H=500;
const MODES={DRAW:"draw",STIFFNESS:"stiffness",ANISO:"aniso",PIN:"pin",FORCE:"force",SIMULATE:"simulate",GROW:"grow"};
const PRESETS=[
  {label:"Rectangle",fn:()=>makeRect(350,250,220,140)},
  {label:"Hexagon",fn:()=>makeHex(350,250,110)},
  {label:"Circle",fn:()=>makeCircle(350,250,110,20)},
  {label:"Leaf",fn:()=>makeLeaf(350,250,220)},
  //{label:"Bilayer Strip",fn:()=>makeStrip(350,250,400,70,16), /old bilayer
   // postProcess:(verts,eds)=>{
    //  let minY=Infinity,maxY=-Infinity,minX=Infinity;
    //  for(const v of verts){if(v.y<minY)minY=v.y;if(v.y>maxY)maxY=v.y;if(v.x<minX)minX=v.x;}
    //  const midY=(minY+maxY)/2;
    //  return {
    //    edges:eds.map(ed=>({...ed,stiffness:(verts[ed.i].y+verts[ed.j].y)/2<midY?2.5:0.3})),
    //    vertices:verts.map(v=>({...v,pinned:v.x<minX+5})),
    //  };
    //}
 // },
];
const OVERLAY_MODES={NONE:"none",STRESS:"stress",DISP:"disp",ARROWS:"arrows"};

const COL={
  bg:"#111418",panel:"#1a1e24",panelBorder:"#2a3040",text:"#e8ecf2",textMuted:"#9aa5b8",
  textDim:"#6b7a90",accent:"#5b9cf5",accentGreen:"#5cc98e",accentWarm:"#f0a050",danger:"#e86060",
  btnBg:"#232a34",btnBorder:"#3a4560",btnActiveBg:"#2a3a55",btnActiveBorder:"#5b9cf5",canvasBg:"#0d1117",
};
const panelStyle={background:COL.panel,border:`1px solid ${COL.panelBorder}`,borderRadius:"10px",padding:"14px"};
const btnBase={padding:"7px 12px",borderRadius:"6px",fontSize:"13px",fontFamily:"'Inter', system-ui, sans-serif",cursor:"pointer",transition:"all 0.15s",fontWeight:500};
const makeBtn=(active,enabled=true)=>({...btnBase,border:`1.5px solid ${active?COL.btnActiveBorder:COL.btnBorder}`,background:active?COL.btnActiveBg:COL.btnBg,color:active?"#fff":enabled?COL.text:COL.textDim,cursor:enabled?"pointer":"not-allowed",opacity:enabled?1:0.5});
const smallBtn={...btnBase,padding:"5px 10px",fontSize:"12px",border:`1px solid ${COL.btnBorder}`,background:COL.btnBg,color:COL.text};
const labelStyle={fontSize:"13px",color:COL.textMuted,display:"block",marginBottom:"4px"};
const strongVal={color:"#fff",fontWeight:600};
const sliderStyle={width:"100%",accentColor:COL.accent,marginTop:"4px"};
const headingStyle={fontSize:"15px",fontWeight:700,color:"#fff",marginBottom:"10px",display:"flex",alignItems:"center",gap:"6px"};

function AnisotropyDirectionField({vertices, edges}) {
  return edges.map((ed,k) => {
    const a=vertices[ed.i],b=vertices[ed.j]; if(!a||!b) return null;
    const ratio = ed.aniso?.ratio ?? 1;
    if(ratio>0.98) return null;
    const angle = ed.aniso?.angle ?? 0;
    const mx=(a.x+b.x)/2, my=(a.y+b.y)/2;
    const arrowLen = dist(a,b)*0.7;
    const px=Math.cos(angle)*arrowLen/2, py=Math.sin(angle)*arrowLen/2;
    const degree=Math.min(Math.max(1-ratio,0),1);
    const [vr,vg,vb]=viridis(degree);
    return (
      <line key={k} x1={mx-px} y1={my-py} x2={mx+px} y2={my+py} stroke={`rgb(${vr},${vg},${vb})`} strokeWidth="1.5" strokeLinecap="round" opacity="0.95"/>
    );
  });
}

export default function PlantBiomechanicsSim() {
  const [mode,setMode]=useState(MODES.DRAW);
  const [drawPoints,setDrawPoints]=useState([]);
  const [vertices,setVertices]=useState([]);
  const [edges,setEdges]=useState([]);
  const [triangles,setTriangles]=useState([]);
  const [nBoundary,setNBoundary]=useState(0);
  const [restVertices,setRestVertices]=useState([]);
  const [pressure,setPressure]=useState(0);
  const [externalForces,setExternalForces]=useState([]);
  const [running,setRunning]=useState(false);
  const [subdivMaxEdge,setSubdivMaxEdge]=useState(40);
  const [snapToGrid,setSnapToGrid]=useState(true);
  const [forceNorm,setForceNorm]=useState(0);
  const [brushStiffness,setBrushStiffness]=useState(1.0);
  const [brushRadius,setBrushRadius]=useState(50);
  const [forceStrength,setForceStrength]=useState(30);
  const [forceDir,setForceDir]=useState("down");
  const [showRest,setShowRest]=useState(true);
  const [hoveredVertex,setHoveredVertex]=useState(null);
  const [brushPos,setBrushPos]=useState(null);
  const [isPainting,setIsPainting]=useState(false);
  const [overlayMode,setOverlayMode]=useState(OVERLAY_MODES.NONE);
  const [growTolerance,setGrowTolerance]=useState(0.5);
  const [growRate,setGrowRate]=useState(0.05);
  const [growCycles,setGrowCycles]=useState(0);
  const growCyclesRef=useRef(0);
  const [zoom,setZoom]=useState(1);
  const [pan,setPan]=useState({x:0,y:0});
  const [isPanning,setIsPanning]=useState(false);
  const panStart=useRef({x:0,y:0,panX:0,panY:0});
  
  const cgStateRef = useRef({ prevForces: null, searchDirections: null, currentForces: null, isFirstStep: true });

  const [anisoAngle,setAnisoAngle]=useState(0);
  const [anisoRatio,setAnisoRatio]=useState(0.2);
  const [showAnisoField,setShowAnisoField]=useState(true);
  const svgRef=useRef(null);
  const animRef=useRef(null);

  const boundaryEdgeIndices=useMemo(()=>edges.reduce((a,e,i)=>{if(e.isBoundary)a.push(i);return a;},[]),[edges]);
  const ek=(a,b)=>a<b?`${a}-${b}`:`${b}-${a}`;

  const trianglesWithEdges=useMemo(()=>{
    const edgeMap={};
    edges.forEach((e,i)=>{edgeMap[ek(e.i,e.j)]=i;});
    return triangles.map(t=>({...t,ea:edgeMap[ek(t.a,t.b)]??0,eb:edgeMap[ek(t.b,t.c)]??0,ec:edgeMap[ek(t.c,t.a)]??0}));
  },[triangles,edges]);

  const edgeStress=useMemo(()=>{
    if(overlayMode!==OVERLAY_MODES.STRESS||restVertices.length===0) return null;
    return computeEdgeStress(vertices,edges,restVertices);
  },[overlayMode,vertices,edges,restVertices]);
  const vertexDisp=useMemo(()=>{
    if((overlayMode!==OVERLAY_MODES.DISP&&overlayMode!==OVERLAY_MODES.ARROWS)||restVertices.length===0) return null;
    return computeVertexDisplacement(vertices,restVertices);
  },[overlayMode,vertices,restVertices]);
  const maxEdgeStress=useMemo(()=>edgeStress?Math.max(...edgeStress,0.001):1,[edgeStress]);
  const maxVertexDisp=useMemo(()=>vertexDisp?Math.max(...vertexDisp,0.001):1,[vertexDisp]);
  const triStress=useMemo(()=>{
    if(!edgeStress) return null;
    return trianglesWithEdges.map(t=>(((edgeStress[t.ea]||0)+(edgeStress[t.eb]||0)+(edgeStress[t.ec]||0))/3));
  },[edgeStress,trianglesWithEdges]);
  const triDisp=useMemo(()=>{
    if(!vertexDisp) return null;
    return trianglesWithEdges.map(t=>(((vertexDisp[t.a]||0)+(vertexDisp[t.b]||0)+(vertexDisp[t.c]||0))/3));
  },[vertexDisp,trianglesWithEdges]);
  const dispArrows=useMemo(()=>{
    if(overlayMode!==OVERLAY_MODES.ARROWS||restVertices.length===0) return [];
    return buildDisplacementArrows(vertices,restVertices);
  },[overlayMode,vertices,restVertices]);

  const edgesRef=useRef(edges);
  const growToleranceRef=useRef(growTolerance);
  const growRateRef=useRef(growRate);
  const modeRef=useRef(mode);
  useEffect(()=>{edgesRef.current=edges;},[edges]);
  useEffect(()=>{growToleranceRef.current=growTolerance;},[growTolerance]);
  useEffect(()=>{growRateRef.current=growRate;},[growRate]);
  useEffect(()=>{modeRef.current=mode;},[mode]);

  useEffect(()=>{
    if(!running){
      if(animRef.current) cancelAnimationFrame(animRef.current);
      cgStateRef.current = { prevForces: null, searchDirections: null, currentForces: null, isFirstStep: true };
      return;
    }
    let frameId;
    const step=()=>{
      setVertices(prev=>{
        const eds=edgesRef.current;
        const {verts:next,forceNorm}=simulateStep(prev,eds,boundaryEdgeIndices,pressure,externalForces,cgStateRef.current);
        
        let cx=0, cy=0;
        for (let i=0; i<next.length; i++) { cx += next[i].x; cy += next[i].y; }
        cx /= next.length; cy /= next.length;
        
        // Mutate positions in-place to center, avoiding another array allocation (.map)
        const ox=CANVAS_W/2-cx, oy=CANVAS_H/2-cy;
        for (let i=0; i<next.length; i++) {
          next[i].x += ox;
          next[i].y += oy;
        }
        
        setForceNorm(forceNorm);
        if(modeRef.current===MODES.GROW){
          if(forceNorm<=growToleranceRef.current){
            setEdges(curEds=>curEds.map(ed=>{
              const a=next[ed.i],b=next[ed.j]; if(!a||!b) return ed;
              const cur=dist(a,b),delta=(cur-ed.restLength)*growRateRef.current;
              return {...ed,restLength:ed.restLength+delta};
            }));
            growCyclesRef.current+=1; setGrowCycles(growCyclesRef.current);
          }
        }
        return next;
      });
      frameId=requestAnimationFrame(step);
      animRef.current=frameId;
    };
    frameId=requestAnimationFrame(step);
    animRef.current=frameId;
    return()=>cancelAnimationFrame(frameId);
  },[running,boundaryEdgeIndices,pressure,externalForces]);

  const svgCoords=useCallback((e)=>{
    const svg=svgRef.current; if(!svg) return{x:0,y:0};
    const rect=svg.getBoundingClientRect();
    const vw=CANVAS_W/zoom,vh=CANVAS_H/zoom;
    const cx=CANVAS_W/2-pan.x,cy=CANVAS_H/2-pan.y;
    return{x:cx-vw/2+((e.clientX-rect.left)/rect.width)*vw,y:cy-vh/2+((e.clientY-rect.top)/rect.height)*vh};
  },[zoom,pan]);

  const initMesh=useCallback((boundaryPts,postProcess)=>{
    const mesh=buildMesh(boundaryPts,subdivMaxEdge);
    let verts=mesh.vertices,eds=mesh.edges;
    if(postProcess){const r=postProcess(verts,eds);verts=r.vertices;eds=r.edges;}
    setVertices(verts);setRestVertices(verts.map(v=>({...v})));setEdges(eds);setTriangles(mesh.triangles);
    setNBoundary(mesh.nBoundary);setDrawPoints([]);setExternalForces([]);setRunning(false);
    cgStateRef.current = { prevForces: null, searchDirections: null, currentForces: null, isFirstStep: true };
    growCyclesRef.current=0;setGrowCycles(0);setMode(MODES.STIFFNESS);
  },[subdivMaxEdge]);

  const finishShape=useCallback(()=>{if(drawPoints.length>=3)initMesh(drawPoints);},[drawPoints,initMesh]);
  const loadPreset=useCallback((preset)=>initMesh(preset.fn(),preset.postProcess),[initMesh]);
  const resetShape=useCallback(()=>{setVertices([]);setEdges([]);setTriangles([]);setRestVertices([]);setDrawPoints([]);setExternalForces([]);setPressure(0);setRunning(false);setNBoundary(0);growCyclesRef.current=0;setGrowCycles(0);cgStateRef.current = { prevForces: null, searchDirections: null, currentForces: null, isFirstStep: true };setMode(MODES.DRAW);},[]);
  const resetDeformation=useCallback(()=>{
    if(restVertices.length===0) return;
    setRunning(false); growCyclesRef.current=0; setGrowCycles(0);
    cgStateRef.current = { prevForces: null, searchDirections: null, currentForces: null, isFirstStep: true };
    setVertices(restVertices.map(v=>({...v,vx:0,vy:0})));
    setEdges(prev=>prev.map(ed=>({...ed,restLength:dist(restVertices[ed.i],restVertices[ed.j])})));
  },[restVertices]);

  const paintStiffness=useCallback((pt)=>{
    setEdges(prev=>prev.map(ed=>{
      const vA=vertices[ed.i],vB=vertices[ed.j]; if(!vA||!vB) return ed;
      const mx=(vA.x+vB.x)/2,my=(vA.y+vB.y)/2;
      return dist(pt,{x:mx,y:my})<=brushRadius?{...ed,stiffness:brushStiffness}:ed;
    }));
  },[vertices,brushRadius,brushStiffness]);

  const paintAniso=useCallback((pt)=>{
    const angleRad=anisoAngle*(Math.PI/180);
    setEdges(prev=>prev.map(ed=>{
      const vA=vertices[ed.i],vB=vertices[ed.j]; if(!vA||!vB) return ed;
      const mx=(vA.x+vB.x)/2,my=(vA.y+vB.y)/2;
      return dist(pt,{x:mx,y:my})<=brushRadius?{...ed,aniso:{angle:angleRad,ratio:anisoRatio}}:ed;
    }));
  },[vertices,brushRadius,anisoAngle,anisoRatio]);

  const findNearestVertex=useCallback((pt)=>{let best=-1,bestD=18;for(let k=0;k<vertices.length;k++){const d=dist(pt,vertices[k]);if(d<bestD){bestD=d;best=k;}}return best;},[vertices]);

  const handleMouseDown=useCallback((e)=>{
    const pt=svgCoords(e);
    if((mode===MODES.SIMULATE||mode===MODES.GROW)&&e.button===0){setIsPanning(true);panStart.current={x:e.clientX,y:e.clientY,panX:pan.x,panY:pan.y};return;}
    if(mode===MODES.DRAW){
      const snapped=snapToGrid?{x:Math.round(pt.x/40)*40,y:Math.round(pt.y/40)*40}:pt;
      setDrawPoints(prev=>[...prev,snapped]);
    }
    else if(mode===MODES.STIFFNESS){setIsPainting(true);paintStiffness(pt);}
    else if(mode===MODES.ANISO){setIsPainting(true);paintAniso(pt);}
    else if(mode===MODES.PIN){const vi=findNearestVertex(pt);if(vi>=0)setVertices(prev=>prev.map((v,k)=>k===vi?{...v,pinned:!v.pinned}:v));cgStateRef.current.isFirstStep=true;}
    else if(mode===MODES.FORCE){const vi=findNearestVertex(pt);if(vi>=0)setExternalForces(prev=>{const ex=prev.findIndex(f=>f.vertexIndex===vi);cgStateRef.current.isFirstStep=true;if(ex>=0)return prev.filter((_,i)=>i!==ex);const fd=forceDir==="down"?{fx:0,fy:forceStrength}:forceDir==="up"?{fx:0,fy:-forceStrength}:forceDir==="left"?{fx:-forceStrength,fy:0}:{fx:forceStrength,fy:0};return[...prev,{vertexIndex:vi,...fd}];});}
  },[mode,svgCoords,paintStiffness,paintAniso,findNearestVertex,forceStrength,forceDir,pan,snapToGrid]);

  const handleMouseMove=useCallback((e)=>{
    if(isPanning){
      const svg=svgRef.current; if(!svg) return;
      const rect=svg.getBoundingClientRect();
      const dx=(e.clientX-panStart.current.x)/rect.width*CANVAS_W/zoom;
      const dy=(e.clientY-panStart.current.y)/rect.height*CANVAS_H/zoom;
      setPan({x:panStart.current.panX+dx,y:panStart.current.panY+dy}); return;
    }
    const pt=svgCoords(e);
    if(mode===MODES.STIFFNESS){setBrushPos(pt);if(isPainting)paintStiffness(pt);}
    else if(mode===MODES.ANISO){setBrushPos(pt);if(isPainting)paintAniso(pt);}
    else if(mode===MODES.PIN||mode===MODES.FORCE){setHoveredVertex(findNearestVertex(pt)??null);setBrushPos(null);}
    else{setBrushPos(null);setHoveredVertex(null);}
  },[mode,svgCoords,isPainting,paintStiffness,paintAniso,findNearestVertex,isPanning,zoom]);

  const handleMouseUp=useCallback((e)=>{setIsPainting(false);if(e===undefined||e.button===0||e.button===1)setIsPanning(false);},[]);
  const handleMouseLeave=useCallback(()=>{setIsPainting(false);setIsPanning(false);setBrushPos(null);setHoveredVertex(null);},[]);
  const setAllStiffness=useCallback(val=>setEdges(prev=>prev.map(ed=>({...ed,stiffness:val}))),[]);
  const setAllAniso=useCallback(()=>{
    const angleRad=anisoAngle*(Math.PI/180);
    setEdges(prev=>prev.map(ed=>({...ed,aniso:{angle:angleRad,ratio:anisoRatio}})));
  },[anisoAngle,anisoRatio]);
  const resetAllAniso=useCallback(()=>setEdges(prev=>prev.map(ed=>({...ed,aniso:{angle:0,ratio:1.0}}))),[]);

  const hasShape=vertices.length>=3;
  const steps=[
    {mode:MODES.DRAW,label:"Draw",num:"1",enabled:true},
    {mode:MODES.STIFFNESS,label:"Stiffness",num:"2",enabled:hasShape},
    {mode:MODES.ANISO,label:"Anisotropy",num:"3",enabled:hasShape},
    {mode:MODES.PIN,label:"Pin",num:"4",enabled:hasShape},
    {mode:MODES.FORCE,label:"Forces",num:"5",enabled:hasShape},
    {mode:MODES.SIMULATE,label:"Simulate: Turgor",num:"6",enabled:hasShape},
    {mode:MODES.GROW,label:"Simulate: Growth",num:"7",enabled:hasShape},
  ];

  const viewBox=useMemo(()=>{
    const vw=CANVAS_W/zoom,vh=CANVAS_H/zoom;
    const cx=CANVAS_W/2-pan.x,cy=CANVAS_H/2-pan.y;
    return `${cx-vw/2} ${cy-vh/2} ${vw} ${vh}`;
  },[zoom,pan]);

  const handleWheel=useCallback((e)=>{
    e.preventDefault();
    const factor=e.deltaY<0?1.12:1/1.12;
    setZoom(z=>Math.min(Math.max(z*factor,0.3),8));
  },[]);
  useEffect(()=>{
    const svg=svgRef.current; if(!svg) return;
    svg.addEventListener("wheel",handleWheel,{passive:false});
    return()=>svg.removeEventListener("wheel",handleWheel);
  },[handleWheel]);
  const handleMiddleDown=useCallback((e)=>{
    if(e.button===1){e.preventDefault();setIsPanning(true);panStart.current={x:e.clientX,y:e.clientY,panX:pan.x,panY:pan.y};}
  },[pan]);
  const handlePanUp=useCallback((e)=>{if(e.button===1)setIsPanning(false);},[]);
  const resetView=useCallback(()=>{setZoom(1);setPan({x:0,y:0});},[]);

  const restBoundaryPath=restVertices.length>2?restVertices.slice(0,nBoundary).map((v,i)=>`${i===0?"M":"L"}${v.x},${v.y}`).join(" ")+" Z":"";
  const drawPath=drawPoints.length>0?drawPoints.map((p,i)=>`${i===0?"M":"L"}${p.x},${p.y}`).join(" "):"";
  const isSimMode=mode===MODES.SIMULATE||mode===MODES.GROW;
  const isBrushMode=mode===MODES.STIFFNESS||mode===MODES.ANISO;

  const anisoAngleRad=anisoAngle*(Math.PI/180);
  const brushTickLen=20;

  return (
    <div style={{fontFamily:"'Inter', system-ui, -apple-system, sans-serif",background:COL.bg,color:COL.text,minHeight:"100vh",padding:"16px",boxSizing:"border-box"}}>
      <style>{`@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap');*{box-sizing:border-box;}input[type=range]{height:6px;}`}</style>

      <div style={{textAlign:"center",marginBottom:"14px"}}>
        <h1 style={{fontSize:"24px",fontWeight:700,color:"#fff",margin:"0 0 4px 0",letterSpacing:"-0.5px"}}>
          🌱 Plant Cell Biomechanics Lab
        </h1>
        <p style={{fontSize:"14px",color:COL.textMuted,margin:0}}>
          Draw · Paint stiffness & anisotropy · Apply turgor pressure · Visualise static stress fields via Conjugate Gradient
        </p>
      </div>

      <div style={{display:"flex",gap:"6px",justifyContent:"center",marginBottom:"14px",flexWrap:"wrap"}}>
        {steps.map(s=>(
          <button key={s.mode} disabled={!s.enabled}
            onClick={()=>{if(s.mode!==MODES.SIMULATE&&s.mode!==MODES.GROW)setRunning(false);setMode(s.mode);}}
            style={{...makeBtn(mode===s.mode,s.enabled),padding:"8px 14px",display:"flex",alignItems:"center",gap:"6px"}}>
            <span style={{display:"inline-flex",alignItems:"center",justifyContent:"center",width:20,height:20,borderRadius:"50%",fontSize:"11px",fontWeight:700,background:mode===s.mode?COL.accent:"#333c4a",color:mode===s.mode?"#fff":"#8895a8"}}>{s.num}</span>
            {s.label}
          </button>
        ))}
      </div>

      <div style={{display:"flex",gap:"14px",justifyContent:"center",flexWrap:"wrap"}}>
        <div style={{width:"215px",flexShrink:0,display:"flex",flexDirection:"column",gap:"10px"}}>
          <div style={panelStyle}>

            {mode===MODES.DRAW&&(<>
              <div style={headingStyle}>✏️ Draw Shape</div>
              <p style={{fontSize:"13px",lineHeight:1.7,color:COL.textMuted,margin:"0 0 12px 0"}}>
                Click on the canvas to place vertices (min 3), then close the shape.
              </p>
              <label style={{display:"flex",alignItems:"center",gap:"6px",fontSize:"13px",marginBottom:"12px",cursor:"pointer",color:COL.textMuted}}>
                <input type="checkbox" checked={snapToGrid} onChange={e=>setSnapToGrid(e.target.checked)} style={{accentColor:COL.accent}}/>
                Snap vertices to grid
              </label>
              <label style={labelStyle}>Edge subdivide: <span style={strongVal}>{subdivMaxEdge===0?"Off":`≤${subdivMaxEdge}px`}</span></label>
              <input type="range" min="0" max="80" step="5" value={subdivMaxEdge} onChange={e=>setSubdivMaxEdge(parseInt(e.target.value))} style={sliderStyle}/>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"12px"}}><span>Off</span><span>Fine</span></div>
              <button onClick={finishShape} disabled={drawPoints.length<3} style={{...makeBtn(false,drawPoints.length>=3),width:"100%",background:drawPoints.length>=3?COL.accent:COL.btnBg,color:drawPoints.length>=3?"#fff":COL.textDim,fontWeight:600}}>
                Close & Mesh ({drawPoints.length} pts)
              </button>
              <div style={{marginTop:"14px",fontSize:"12px",color:COL.textDim,textAlign:"center",marginBottom:"6px"}}>— or pick a preset —</div>
              <div style={{display:"flex",flexWrap:"wrap",gap:"5px"}}>
                {PRESETS.map(p=>(<button key={p.label} onClick={()=>loadPreset(p)} style={{...smallBtn,flex:"1 0 45%"}}>{p.label}</button>))}
              </div>
            </>)}

            {mode===MODES.STIFFNESS&&(<>
              <div style={headingStyle}>🌿 Paint Stiffness</div>
              <label style={labelStyle}>Stiffness: <span style={{...strongVal,color:stiffnessLabelColor(brushStiffness)}}>{brushStiffness.toFixed(1)}</span></label>
              <input type="range" min="0.1" max="3" step="0.1" value={brushStiffness} onChange={e=>setBrushStiffness(parseFloat(e.target.value))} style={sliderStyle}/>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim}}><span style={{color: '#ffffff'}}>Soft</span><span style={{color: '#ffffff'}}>Stiff</span></div>
              <label style={{...labelStyle,marginTop:"12px"}}>Brush radius: <span style={strongVal}>{brushRadius}px</span></label>
              <input type="range" min="15" max="150" step="5" value={brushRadius} onChange={e=>setBrushRadius(parseInt(e.target.value))} style={sliderStyle}/>
              <button onClick={()=>setAllStiffness(brushStiffness)} style={{...smallBtn,width:"100%",marginTop:"10px"}}>Set All to {brushStiffness.toFixed(1)}</button>
            </>)}

            {mode===MODES.ANISO&&(<>
              <div style={headingStyle}>🧭 Paint Anisotropy</div>
              <p style={{fontSize:"12px",lineHeight:1.6,color:COL.textMuted,margin:"0 0 10px 0"}}>
                Sets a preferred stiff axis. Edges aligned with the axis keep their full stiffness; perpendicular edges are scaled by the ratio.
              </p>

              <label style={labelStyle}>Preferred axis: <span style={strongVal}>{anisoAngle}°</span></label>
              <div style={{position:"relative",width:"100%",marginBottom:"8px"}}>
                <input type="range" min="0" max="179" step="1" value={anisoAngle}
                  onChange={e=>setAnisoAngle(parseInt(e.target.value))} style={sliderStyle}/>
                <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim}}>
                  <span>0° (→)</span><span>90° (↓)</span><span>179°</span>
                </div>
              </div>
              <div style={{display:"flex",justifyContent:"center",marginBottom:"10px"}}>
                <svg width="70" height="70" viewBox="-35 -35 70 70">
                  <circle r="30" fill="#1a2030" stroke="#3a4560" strokeWidth="1"/>
                  {[0,45,90,135].map(a=>{
                    const ar=a*Math.PI/180,cos=Math.cos(ar),sin=Math.sin(ar);
                    return <line key={a} x1={cos*14} y1={sin*14} x2={cos*28} y2={sin*28}
                      stroke="#3a4560" strokeWidth="1" strokeLinecap="round"/>;
                  })}
                  {(() => {
                    const ar=anisoAngle*Math.PI/180;
                    const px=Math.cos(ar)*25,py=Math.sin(ar)*25;
                    const col=anisoColor(1,anisoRatio); // can set the first colour to be ar if want it to change with angles
                    return <>
                      <line x1={-px} y1={-py} x2={px} y2={py} stroke={col} strokeWidth="2.5" strokeLinecap="round"/>
                      <circle r="3" fill={col}/>
                    </>;
                  })()}
                </svg>
              </div>

              <label style={labelStyle}>Anisotropy degree: <span style={strongVal}>{anisoRatio.toFixed(2)}</span></label>
              <input type="range" min="0.01" max="1" step="0.01" value={anisoRatio}
                onChange={e=>setAnisoRatio(parseFloat(e.target.value))} style={sliderStyle}/>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"10px"}}>
                <span>Max aniso</span><span>Isotropic</span>
              </div>

              <label style={{...labelStyle,marginTop:"2px"}}>Brush radius: <span style={strongVal}>{brushRadius}px</span></label>
              <input type="range" min="15" max="150" step="5" value={brushRadius} onChange={e=>setBrushRadius(parseInt(e.target.value))} style={sliderStyle}/>

              <div style={{display:"flex",gap:"5px",marginTop:"10px"}}>
                <button onClick={setAllAniso} style={{...smallBtn,flex:1}}>Set All</button>
                <button onClick={resetAllAniso} style={{...smallBtn,flex:1,color:COL.textDim}}>Reset All</button>
              </div>
              <label style={{display:"flex",alignItems:"center",gap:"6px",fontSize:"13px",marginTop:"10px",cursor:"pointer",color:COL.textMuted}}>
                <input type="checkbox" checked={showAnisoField} onChange={e=>setShowAnisoField(e.target.checked)} style={{accentColor:COL.accent}}/>
                Show direction field
              </label>
            </>)}

            {mode===MODES.PIN&&(<>
              <div style={headingStyle}>📌 Pin Vertices</div>
              <p style={{fontSize:"13px",lineHeight:1.7,color:COL.textMuted,margin:0}}>
                Click a vertex to pin or unpin it. Pinned vertices stay fixed during simulation.
              </p>
            </>)}

            {mode===MODES.FORCE&&(<>
              <div style={headingStyle}>💨 External Forces</div>
              <label style={labelStyle}>Direction</label>
              <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:"5px",marginBottom:"12px"}}>
                {[{k:"up",label:"↑ Up"},{k:"down",label:"↓ Down"},{k:"left",label:"← Left"},{k:"right",label:"→ Right"}].map(d=>(
                  <button key={d.k} onClick={()=>{setForceDir(d.k);setExternalForces(prev=>prev.map(f=>{const fd=d.k==="down"?{fx:0,fy:forceStrength}:d.k==="up"?{fx:0,fy:-forceStrength}:d.k==="left"?{fx:-forceStrength,fy:0}:{fx:forceStrength,fy:0};return{...f,...fd};}));cgStateRef.current.isFirstStep=true;}} style={makeBtn(forceDir===d.k)}>{d.label}</button>
                ))}
              </div>
              <label style={labelStyle}>Strength: <span style={strongVal}>{forceStrength}</span></label>
              <input type="range" min="5" max="80" step="5" value={forceStrength} onChange={e=>{const v=parseFloat(e.target.value);setForceStrength(v);setExternalForces(prev=>prev.map(f=>{const fd=forceDir==="down"?{fx:0,fy:v}:forceDir==="up"?{fx:0,fy:-v}:forceDir==="left"?{fx:-v,fy:0}:{fx:v,fy:0};return{...f,...fd};}));cgStateRef.current.isFirstStep=true;}} style={sliderStyle}/>
            </>)}

            {mode===MODES.SIMULATE&&(<>
              <div style={headingStyle}>▶️ Simulate</div>
              <label style={labelStyle}>Turgor pressure: <span style={strongVal}>{pressure.toFixed(1)}</span></label>
              <input type="range" min="-2" max="5" step="0.1" value={pressure} onChange={e=>{setPressure(parseFloat(e.target.value)); cgStateRef.current.isFirstStep=true;}} style={sliderStyle}/>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"12px"}}><span>Deflate</span><span>High turgor</span></div>
              <div style={{display:"flex",gap:"6px"}}>
                <button onClick={()=>setRunning(r=>!r)} style={{...makeBtn(false,true),flex:1,fontWeight:600,textAlign:"center",background:running?"#3a2020":COL.accentGreen,borderColor:running?"#cc5555":COL.accentGreen,color:"#fff"}}>
                  {running?"⏸ Pause":"▶ Run Solver"}
                </button>
                <button onClick={resetDeformation} style={smallBtn}>↺</button>
              </div>
              <div style={{marginTop:"14px",fontSize:"13px",fontWeight:600,color:"#fff",marginBottom:"6px"}}>Field Overlay</div>
              {[
                {k:OVERLAY_MODES.NONE,label:"None"},
                {k:OVERLAY_MODES.STRESS,label:"🔥 Stress"},
                {k:OVERLAY_MODES.DISP,label:"💜 Displacement"},
                {k:OVERLAY_MODES.ARROWS,label:"➡️ Disp. Vectors"},
              ].map(o=>(<button key={o.k} onClick={()=>setOverlayMode(o.k)} style={{...makeBtn(overlayMode===o.k),display:"block",width:"100%",marginBottom:"4px",textAlign:"left"}}>{o.label}</button>))}
              <label style={{display:"flex",alignItems:"center",gap:"6px",fontSize:"13px",marginTop:"10px",cursor:"pointer",color:COL.textMuted}}>
                <input type="checkbox" checked={showRest} onChange={e=>setShowRest(e.target.checked)} style={{accentColor:COL.accent}}/>
                Show rest shape
              </label>
            </>)}

            {mode===MODES.GROW&&(<>
              <div style={headingStyle}>🌱 Growth</div>
              <p style={{fontSize:"13px",lineHeight:1.6,color:COL.textMuted,margin:"0 0 12px 0"}}>
                Runs CG dynamics until residual norm falls below tolerance boundary, then incrementally mutates structural rest lengths.
              </p>
              <label style={labelStyle}>Step tolerance: <span style={strongVal}>{growTolerance.toFixed(2)}</span></label>
              <input type="range" min="0.01" max="20" step="0.01" value={growTolerance} onChange={e=>setGrowTolerance(parseFloat(e.target.value))} style={sliderStyle}/>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"4px"}}><span>Equilibrium</span><span>Far</span></div>
              <div style={{fontSize:"11px",color:COL.textDim,marginBottom:"12px",lineHeight:1.5}}>RMS structural residual norm per node.</div>
              <label style={labelStyle}>Growth rate: <span style={strongVal}>{growRate.toFixed(3)}</span></label>
              <input type="range" min="0.001" max="0.5" step="0.001" value={growRate} onChange={e=>setGrowRate(parseFloat(e.target.value))} style={sliderStyle}/>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"14px"}}><span>Slow</span><span>Fast</span></div>
              <label style={labelStyle}>Turgor pressure: <span style={strongVal}>{pressure.toFixed(1)}</span></label>
              <input type="range" min="-2" max="5" step="0.1" value={pressure} onChange={e=>{setPressure(parseFloat(e.target.value)); cgStateRef.current.isFirstStep=true;}} style={sliderStyle}/>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"14px"}}><span>Deflate</span><span>High</span></div>
              <div style={{display:"flex",gap:"6px"}}>
                <button onClick={()=>setRunning(r=>!r)} style={{...makeBtn(false,true),flex:1,fontWeight:600,textAlign:"center",background:running?"#3a2020":COL.accentGreen,borderColor:running?"#cc5555":COL.accentGreen,color:"#fff"}}>
                  {running?"⏸ Pause":"▶ Grow"}
                </button>
                <button onClick={resetDeformation} style={smallBtn}>↺</button>
              </div>
              <div style={{marginTop:"12px",padding:"8px 10px",background:"#0d1a10",border:"1px solid #1a3a20",borderRadius:"6px",fontSize:"13px"}}>
                <div style={{color:COL.textMuted}}>Growth cycles</div>
                <div style={{fontSize:"22px",fontWeight:700,color:COL.accentGreen}}>{growCycles}</div>
              </div>
            </>)}
          </div>

          {hasShape&&(<button onClick={resetShape} style={{...smallBtn,borderColor:"#553333",color:COL.danger,width:"100%",fontSize:"13px",padding:"7px 10px"}}>🗑 Clear & Redraw</button>)}

          <div style={{...panelStyle,fontSize:"12px",lineHeight:2.2}}>
            <div style={{fontWeight:700,marginBottom:"4px",fontSize:"13px",color:"#fff"}}>Legend</div>
            {mode===MODES.ANISO?(<>
              <div style={{fontSize:"11px",color:COL.textDim,marginBottom:"4px"}}>Mesh — edge stiffness</div>
              <div style={{display:"flex",height:"10px",borderRadius:"3px",overflow:"hidden",marginBottom:"3px"}}>
                {Array.from({length:16},(_,i)=>{const [r,g,b]=viridis(i/15);return <div key={i} style={{flex:1,background:`rgb(${r},${g},${b})`}}/>;})}
              </div>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"10px"}}><span>Soft</span><span>Stiff</span></div>
              <div style={{fontSize:"11px",color:COL.textDim,marginBottom:"4px"}}>Vectors — anisotropy direction</div>
               <div style={{fontSize:"11px",color:COL.textDim,marginBottom:"4px"}}>Vectors — Anisotropy degree</div>
              <div style={{display:"flex",height:"10px",borderRadius:"3px",overflow:"hidden",marginBottom:"3px"}}>
                {Array.from({length:16},(_,i)=>{const [r,g,b]=viridis(i/15);return <div key={i} style={{flex:1,background:`rgb(${r},${g},${b})`}}/>;})}
              </div>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"10px"}}><span>Isotropic</span><span>Anisotropic</span></div>
            </>):(!isSimMode||overlayMode===OVERLAY_MODES.NONE)?(<>
              <div style={{display:"flex",height:"10px",borderRadius:"3px",overflow:"hidden",marginBottom:"3px"}}>
                {Array.from({length:16},(_,i)=>{const [r,g,b]=viridis(i/15);return <div key={i} style={{flex:1,background:`rgb(${r},${g},${b})`}}/>;})}
              </div>
              <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim,marginBottom:"6px"}}><span>Soft</span><span>Stiff</span></div>
              <div style={{display:"flex",alignItems:"center",gap:"8px",color:COL.textMuted}}><div style={{width:12,height:12,borderRadius:"50%",background:"#ffd060",border:"2px solid #aa8030"}}/> Pinned</div>
              <div style={{display:"flex",alignItems:"center",gap:"8px",color:COL.textMuted}}><span style={{color:"#ff6060",fontSize:"15px",fontWeight:700}}>→</span> External force</div>
              <div style={{display:"flex",alignItems:"center",gap:"8px",color:COL.textMuted}}><div style={{width:16,height:0,borderTop:"2px dashed #666"}}/> Rest shape</div>
            </>):(
              <>
                <div style={{fontSize:"11px",color:COL.textDim,marginBottom:"4px"}}>
                  {overlayMode===OVERLAY_MODES.STRESS?"Stress magnitude":"Displacement magnitude"}
                </div>
                <div style={{display:"flex",height:"14px",borderRadius:"4px",overflow:"hidden",marginBottom:"4px"}}>
                  {Array.from({length:20},(_,i)=>{const t=i/19;return <div key={i} style={{flex:1,background:overlayMode===OVERLAY_MODES.STRESS?stressColor(t):dispColor(t)}}/>;} )}
                </div>
                <div style={{display:"flex",justifyContent:"space-between",fontSize:"11px",color:COL.textDim}}><span>Low</span><span>High</span></div>
              </>
            )}
          </div>
        </div>

        <div style={{border:`2px solid ${COL.panelBorder}`,borderRadius:"12px",overflow:"hidden",background:COL.canvasBg,flexShrink:0,position:"relative"}}>
          {isSimMode&&hasShape&&(
            <div style={{position:"absolute",bottom:"10px",left:"10px",zIndex:10,background:"rgba(0,0,0,0.5)",borderRadius:"6px",padding:"4px 8px",fontFamily:"monospace",fontSize:"11px",color:COL.textMuted}}>
              Residual Norm: <span style={{color:"#fff",fontWeight:600}}>{forceNorm.toFixed(4)}</span>
            </div>
          )}
          <div style={{position:"absolute",bottom:"10px",right:"10px",zIndex:10,display:"flex",gap:"4px",alignItems:"center",background:"rgba(0,0,0,0.5)",borderRadius:"6px",padding:"3px 6px"}}>
            <span style={{fontSize:"10px",color:COL.textDim,fontFamily:"monospace"}}>{Math.round(zoom*100)}%</span>
            <button onClick={()=>setZoom(z=>Math.min(z*1.3,8))} style={{...smallBtn,padding:"2px 6px",fontSize:"14px",lineHeight:1}}>+</button>
            <button onClick={()=>setZoom(z=>Math.max(z/1.3,0.3))} style={{...smallBtn,padding:"2px 6px",fontSize:"14px",lineHeight:1}}>−</button>
            <button onClick={resetView} style={{...smallBtn,padding:"2px 8px",fontSize:"10px"}}>⌂</button>
          </div>
          <svg ref={svgRef} viewBox={viewBox} width={CANVAS_W} height={CANVAS_H}
            style={{display:"block",maxWidth:"100%",cursor:isPanning?"grabbing":isSimMode?"grab":isBrushMode?"none":mode===MODES.DRAW?"crosshair":"pointer"}}
             onMouseDown={(e)=>{handleMiddleDown(e);if(e.button===0)handleMouseDown(e);}}
             onMouseMove={handleMouseMove}
             onMouseUp={(e)=>{handlePanUp(e);handleMouseUp(e);}}
           // onMouseDown={handleMouseDown}
            //onMouseMove={handleMouseMove}
           // onMouseUp={handleMouseUp}

  //           onClick={(e) => {
  //   if (hasShape) return;
  //   const rect = e.currentTarget.getBoundingClientRect();
  //   const x = e.clientX - rect.left;
  //   const y = e.clientY - rect.top;

  //   // --- ADD THIS CHECK HERE ---
  //   // Checks if the click is within 5 pixels of any existing point
  //   const isTooClose = drawPoints.some(p => dist(p, { x, y }) < 5);
  //   if (isTooClose) return; // Exit early and do not add the point
  //   // ----------------------------

  //   setDrawPoints([...drawPoints, { x, y }]);
  // }}
            onMouseLeave={handleMouseLeave}
            >
            <defs>
              <pattern id="grid" width="40" height="40" patternUnits="userSpaceOnUse">
                <path d="M 40 0 L 0 0 0 40" fill="none" stroke="#1a2030" strokeWidth="0.5"/>
              </pattern>
              <marker id="arrowhead" markerWidth="6" markerHeight="5" refX="6" refY="2.5" orient="auto">
                <polygon points="0 0, 6 2.5, 0 5" fill="#d060ff"/>
              </marker>
            </defs>
            <rect x="-1000" y="-1000" width="3000" height="3000" fill="url(#grid)"/>

            {showRest&&restBoundaryPath&&isSimMode&&(
              <path d={restBoundaryPath} fill="none" stroke="#444" strokeWidth="1" strokeDasharray="4 3" opacity="0.5"/>
            )}

            {trianglesWithEdges.map((t,k)=>{
              const a=vertices[t.a],b=vertices[t.b],c=vertices[t.c]; if(!a||!b||!c) return null;
              let fill;
              if(mode===MODES.ANISO){
                fill=triFillColor(edges,t);
              } else if(isSimMode&&overlayMode===OVERLAY_MODES.STRESS&&triStress) {
                fill=stressColor(Math.min((triStress[k]||0)/maxEdgeStress,1));
              } else if(isSimMode&&(overlayMode===OVERLAY_MODES.DISP||overlayMode===OVERLAY_MODES.ARROWS)&&triDisp) {
                fill=dispColor(Math.min((triDisp[k]||0)/maxVertexDisp,1));
              } else {
                fill=triFillColor(edges,t);
              }
              return <polygon key={`t${k}`} points={`${a.x},${a.y} ${b.x},${b.y} ${c.x},${c.y}`} fill={fill} stroke="none"/>;
            })}

            {edges.map((ed,k)=>{
              const a=vertices[ed.i],b=vertices[ed.j]; if(!a||!b) return null;
              let stroke,strokeW;
              if(isSimMode&&overlayMode===OVERLAY_MODES.STRESS&&edgeStress){
                stroke=stressColor(Math.min(edgeStress[k]/maxEdgeStress,1));
                strokeW=ed.isBoundary?2.5+ed.stiffness:1;
              } else if(mode===MODES.ANISO){
                stroke=stiffnessEdgeColor(ed.stiffness,ed.isBoundary);
                strokeW=ed.isBoundary?1.5+ed.stiffness*2.5:0.4+ed.stiffness;
              } else {
                stroke=stiffnessEdgeColor(ed.stiffness,ed.isBoundary);
                strokeW=ed.isBoundary?1.5+ed.stiffness*2.5:0.4+ed.stiffness;
              }
              return <line key={`e${k}`} x1={a.x} y1={a.y} x2={b.x} y2={b.y} stroke={stroke} strokeWidth={strokeW} strokeLinecap="round"/>;
            })}

            {mode===MODES.ANISO&&showAnisoField&&vertices.length>0&&(
              <AnisotropyDirectionField vertices={vertices} edges={edges}/>
            )}

            {overlayMode===OVERLAY_MODES.ARROWS&&dispArrows.map((arr,k)=>{
              const scale=Math.min(35/maxVertexDisp,4);
              const ex=arr.x+arr.dx*scale,ey=arr.y+arr.dy*scale;
              const t=Math.min(arr.mag/maxVertexDisp,1);
              return <line key={`da${k}`} x1={arr.x} y1={arr.y} x2={ex} y2={ey}
                stroke={dispColor(t)} strokeWidth="1.5" markerEnd="url(#arrowhead)" opacity="0.85"/>;
            })}

            {vertices.map((v,k)=>{
              const isHov=k===hoveredVertex,hasForce=externalForces.some(f=>f.vertexIndex===k);
              const r=v.pinned?5:isHov?5:v.isBoundary?3:1.5;
              return <circle key={`v${k}`} cx={v.x} cy={v.y} r={r}
                fill={v.pinned?"#ffd060":hasForce?"#ff8060":v.isBoundary?"#90c050":"#6a9a3a"}
                stroke={v.pinned?"#aa8030":isHov?"#fff":"none"} strokeWidth={v.pinned?2:1.5}
                opacity={v.isBoundary||v.pinned||hasForce||isHov?1:0.4}/>;
            })}

            {externalForces.map((ef,k)=>{
              const v=vertices[ef.vertexIndex]; if(!v) return null;
              const mag=Math.sqrt(ef.fx**2+ef.fy**2),arrowLen=Math.min(mag*0.8,40);
              const nx=ef.fx/(mag||1),ny=ef.fy/(mag||1);
              return <line key={`f${k}`} x1={v.x} y1={v.y} x2={v.x+nx*arrowLen} y2={v.y+ny*arrowLen} stroke="#ff6060" strokeWidth="2.5" markerEnd="url(#arrowhead)"/>;
            })}

            {brushPos&&isBrushMode&&(
              <>
                <circle cx={brushPos.x} cy={brushPos.y} r={brushRadius}
                  fill={mode===MODES.ANISO?`${anisoColor(anisoAngleRad,anisoRatio)}22`:`${stiffnessLabelColor(brushStiffness)}11`}
                  stroke={mode===MODES.ANISO?anisoColor(anisoAngleRad,anisoRatio):stiffnessLabelColor(brushStiffness)}
                  strokeWidth="1.5" strokeDasharray="5 3" opacity="0.8"/>
                {mode===MODES.ANISO&&(() => {
                  const px=Math.cos(anisoAngleRad)*brushTickLen,py=Math.sin(anisoAngleRad)*brushTickLen;
                  const col=anisoColor(anisoAngleRad,anisoRatio);
                  return <line x1={brushPos.x-px} y1={brushPos.y-py} x2={brushPos.x+px} y2={brushPos.y+py}
                    stroke={col} strokeWidth="2.5" strokeLinecap="round"/>;
                })()}
              </>
            )}

            {drawPoints.map((p,k)=>(<circle key={`dp${k}`} cx={p.x} cy={p.y} r="5" fill="#fff" stroke={COL.accent} strokeWidth="2"/>))}
            {drawPath&&<path d={drawPath} fill="none" stroke="#fff" strokeWidth="2" strokeDasharray="6 4"/>}
            {drawPoints.length>=3&&(
              <line x1={drawPoints[drawPoints.length-1].x} y1={drawPoints[drawPoints.length-1].y}
                x2={drawPoints[0].x} y2={drawPoints[0].y} stroke="#fff" strokeWidth="1" strokeDasharray="3 4" opacity="0.4"/>
            )}

            {!hasShape&&drawPoints.length===0&&(
              <text x={CANVAS_W/2} y={CANVAS_H/2} textAnchor="middle" fontSize="15" fill={COL.textDim} fontFamily="Inter, system-ui, sans-serif">
                Click to place vertices, or pick a preset →
              </text>
            )}
          </svg>
        </div>
      </div>

      <div style={{textAlign:"center",marginTop:"14px",fontSize:"11px",color:COL.textDim,lineHeight:1.6}}>
        Vertex-spring system · Fletcher–Reeves Conjugate Gradient Solver · Anisotropic stiffness relaxation
      </div>
    </div>
  );
}