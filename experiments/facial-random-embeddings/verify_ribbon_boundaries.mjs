#!/usr/bin/env node
"use strict";
// Independent physical ribbon-band audit. This implementation was developed
// separately from the permutation-cycle implementation. No dependencies.
// Run: node verify_ribbon_boundaries.mjs [certificate.json]
// Flags (v,w,s) are the two corners of the v-end of edge vw.
// C pairs adjacent corners around a vertex disk. B pairs corners along bands.
// Our twist bit 0 is untwisted; the author's lambda bit is its complement.
import fs from "node:fs";
import assert from "node:assert/strict";
const V = [0,1,2,3], E = [];
for (let u=0;u<4;u++) for(let v=u+1;v<4;v++) E.push([u,v]);
function embedding(rotmask,tmask) {
 const flags=[],idx={};
 for(let e=0;e<E.length;e++)for(let endpoint=0;endpoint<2;endpoint++)for(let side=0;side<2;side++){const [u,v]=E[e];idx[[E[e][endpoint],E[e][1-endpoint],side]]=flags.length;flags.push({v:E[e][endpoint],w:E[e][1-endpoint],side,e});}
 let C=[],B=[]; for(let i=0;i<flags.length;i++){
  const {v,w,side,e}=flags[i];let nbr=V.filter(x=>x!==v);if((rotmask>>v)&1)nbr.reverse();
  const j=nbr.indexOf(w); const next=nbr[(j+(side===1?1:2))%3];
  C[i]=idx[[v,next,1-side]];B[i]=idx[[w,v,side^1^((tmask>>e)&1)]];
 }
 const visited=new Set(),faces=[],occ=E.map(()=>[]);
 for(let i=0;i<flags.length;i++){if(visited.has(i))continue;let x=i,walk=[];do{visited.add(x);visited.add(B[x]);let f=flags[x];occ[f.e].push([faces.length,f.v]);walk.push([f.v,f.w]);x=C[B[x]];}while(x!==i);faces.push(walk);}
 let counts=[0,0,0],types=[];
 for(let e=0;e<E.length;e++){if(occ[e].length!==2)throw Error("occ");const [a,b]=occ[e];const type=a[0]!==b[0]?2:a[1]===b[1]?0:1;counts[type]++;types.push(type);}
 // orientable iff edge twist cochain is cut
 let orientable=false;for(let vm=0;vm<16;vm++){if(E.every(([u,v],e)=>(((vm>>u)^(vm>>v)^(tmask>>e))&1)===0)){orientable=true;break;}}
 return {counts,types,faces,orientable,C,B};
}

function gcd(a,b){while(b){[a,b]=[b,a%b];}return a;}
function ratio(a,b){const d=gcd(a,b);return b/d===1?String(a/d):`${a/d}/${b/d}`;}
function perms(a){if(!a.length)return [[]];return a.flatMap(x=>perms(a.filter(y=>y!==x)).map(p=>[x,...p]));}
function cycles(P){
  const seen=new Set(), out=[];
  for(let i=0;i<P.length;i++){
    if(seen.has(i))continue;
    const c=[];let x=i;
    do{assert(!seen.has(x));seen.add(x);c.push(x);x=P[x];}while(x!==i);
    out.push(c);
  }
  return out;
}
// Independent re-expression of the notebook's pair comparisons, after the
// physical boundary classifier above had already produced its answer.
function notebookCount(P){
  let good=0,bad=0;
  for(const c of cycles(P))for(let i=0;i<c.length;i++)for(let j=i+1;j<c.length;j++){
    const a=c[i],b=c[j];
    if(Math.floor(a/4)!==Math.floor(b/4))continue; // different underlying edges
    if(Math.floor(a/2)===Math.floor(b/2))good++;else bad++;
  }
  assert(good%2===0 && bad%2===0);
  return [good/2,bad/2,6-(good+bad)/2];
}
function delta(mask){
  let out=0;E.forEach(([u,v],e)=>{if(((mask>>u)^(mask>>v))&1)out|=1<<e;});
  return out;
}
function relabelTwists(t,p) {
  let rr=0,tt=0;
  for(let v=0;v<4;v++){
    const newN=V.filter(w=>w!==v).map(w=>p[w]);
    const standard=V.filter(w=>w!==p[v]);
    const k=standard.indexOf(newN[0]);
    if(standard[(k+1)%3]!==newN[1])rr|=1<<p[v];
  }
  for(let e=0;e<6;e++){
    const pair=E[e].map(v=>p[v]).sort();
    const ei=E.findIndex(x=>x[0]===pair[0]&&x[1]===pair[1]);
    tt|=((t>>e)&1)<<ei;
  }
  return tt^delta(rr); // restore every cyclic order to the ascending reference
}
function connectedFlags(C,B){
  const reached=new Set([0]), queue=[0];
  for(let k=0;k<queue.length;k++)for(const y of [C[queue[k]],B[queue[k]],queue[k]^1]){
    if(!reached.has(y)){reached.add(y);queue.push(y);}
  }
  return reached.size===24;
}
const total=[0,0,0],hist={},bySurface={},conditional={},fixedRows=[];
const perEdge=E.map(()=>[0,0,0]);
let gaugeChecks=0,twistChecks=0,notebookChecks=0,compositionChecks=0,connectivityChecks=0;
const cache=Array.from({length:16},(_,r)=>Array.from({length:64},(_,t)=>embedding(r,t)));
for(let r=0;r<16;r++)for(let t=0;t<64;t++){
  const a=cache[r][t];
  a.counts.forEach((n,i)=>total[i]+=n);
  a.types.forEach((ty,e)=>perEdge[e][ty]++);
  hist[a.counts]=(hist[a.counts]||0)+1;
  const f=a.faces.length,chi=f-2;
  assert(chi<=2);
  if(a.orientable){assert((2-chi)%2===0);assert(a.counts[0]===0);}
  else assert(2-chi>=1);
  for(const face of a.faces)for(let k=0;k<face.length;k++)
    assert(face[k][1]===face[(k+1)%face.length][0]);
  assert(a.faces.reduce((n,x)=>n+x.length,0)===12);
  for(let i=0;i<24;i++){
    assert(a.C[a.C[i]]===i && a.B[a.B[i]]===i);
    assert(a.C[i]!==i && a.B[i]!==i);
  }
  assert(connectedFlags(a.C,a.B));connectivityChecks++;
  const sk=(a.orientable?"orientable":"nonorientable")+","+f;
  bySurface[sk]??={samples:0,totals:[0,0,0],chi};
  bySurface[sk].samples++;
  a.counts.forEach((n,i)=>bySurface[sk].totals[i]+=n);
  const ok=a.orientable?"orientable":"nonorientable";
  conditional[ok]??={samples:0,totals:[0,0,0]};
  conditional[ok].samples++;
  a.counts.forEach((n,i)=>conditional[ok].totals[i]+=n);
  const cb=Array.from({length:24},(_,i)=>a.C[a.B[i]]);
  const bc=Array.from({length:24},(_,i)=>a.B[a.C[i]]);
  assert.deepStrictEqual(notebookCount(cb),a.counts);notebookChecks++;
  assert.deepStrictEqual(notebookCount(bc),a.counts);compositionChecks++;
  assert(cycles(cb).length===2*f);
  for(let flip=0;flip<16;flip++){
    const b=cache[r^flip][t^delta(flip)];
    assert.deepStrictEqual(a.types,b.types);
    assert(a.faces.length===b.faces.length && a.orientable===b.orientable);
    gaugeChecks++;
  }
  for(let e=0;e<6;e++){
    const b=cache[r][t^(1<<e)];
    assert(b.types[e]===[2,1,0][a.types[e]]); // good <-> regular, bad stays bad
    twistChecks++;
  }
  if(r===0)fixedRows.push({twist_mask:t,counts:a.counts,edge_types:a.types,faces:f,orientable:a.orientable});
}
assert.deepStrictEqual(total,[2208,1728,2208]);
assert.deepStrictEqual(perEdge,Array.from({length:6},()=>[368,288,368]));
const ps=perms(V),left=new Set(Array.from({length:64},(_,i)=>i)),orbits=[];
while(left.size){
  const t=left.values().next().value;
  const members=[...new Set(ps.map(p=>relabelTwists(t,p)))].sort((a,b)=>a-b);
  for(const u of members){
    assert(left.has(u));left.delete(u);
    assert.deepStrictEqual(cache[0][t].counts,cache[0][u].counts);
    assert(cache[0][t].faces.length===cache[0][u].faces.length);
    assert(cache[0][t].orientable===cache[0][u].orientable);
  }
  orbits.push({representative:t,size:members.length,members,counts:cache[0][t].counts,
    faces:cache[0][t].faces.length,orientable:cache[0][t].orientable});
}
assert(orbits.length===11);
const unlabeledTotals=orbits.reduce((a,o)=>a.map((x,i)=>x+o.counts[i]),[0,0,0]);
for(const item of Object.values(conditional))item.expectations=item.totals.map(n=>ratio(n,item.samples));
const fixedTotals=fixedRows.reduce((a,row)=>a.map((x,i)=>x+row.counts[i]),[0,0,0]);
const certificate={
  graph:"K4",vertices:V,edges:E,type_order:["good","bad","regular"],
  twist_convention:"Bit 0 untwisted. Notebook lambda t = 1 - this bit.",
  samples:1024,totals:total,expectations:total.map(n=>ratio(n,1024)),
  per_edge_counts:perEdge,per_edge_probabilities:perEdge[0].map(n=>ratio(n,1024)),
  conjectured_expectations:["2","2","2"],histogram:hist,
  gauge_quotient:{group:"Independent reversal of each vertex disk orientation",
    action:"(r,t) -> (r xor flip, t xor delta(flip))",
    orbit_size:16,orbits:64,fixed_rotation_totals:fixedTotals,
    expectations:fixedTotals.map(n=>ratio(n,64)),
    warning:"This gauge quotient retains vertex and edge labels. It is not the graph-isomorphism quotient."},
  graph_isomorphism_quotient:{group:"Aut(K4) = S4 acting on the 64 gauge classes",
    orbits:orbits.length,uniform_unlabelled_totals:unlabeledTotals,
    uniform_unlabelled_expectations:unlabeledTotals.map(n=>ratio(n,orbits.length)),
    warning:"The author's sampler gives these orbits probability size/64, not equal probability.",
    classes:orbits},
  surface_counts:bySurface,conditional_expectations:conditional,
  checks:{gaugeChecks,twistChecks,notebookChecks,compositionChecks,connectivityChecks,
    boundary_occurrences_per_embedding:12,oriented_phi_cycles_per_physical_face:2},
  fixed_rotation_enumeration:fixedRows,
  source_fidelity:{
    paper:"https://arxiv.org/html/2605.01410v1#S4",
    notebook:"https://github.com/babakghanbari993/cdc-random-embeddings/blob/0d4404941894d3ef8dd9f27f1e61829bec2bcde5/notebooks/random_embedding_experiment.ipynb",
    notebook_blob_sha:"82fb13311d4c9ef254d644ab021346915e61618a",
    notebook_kernel:"SageMath 10.1",
    sage_convention:"https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/permutation.html",
    caveat:"Paper Section 4 does not explicitly define a probability measure. This exact refutation uses the pinned author notebook sampler and its equivalent signed-rotation gauge quotient. No native Sage process was run."
  }
};
const out=JSON.stringify(certificate,null,2)+"\n";
if(process.argv[2])fs.writeFileSync(process.argv[2],out);else process.stdout.write(out);

