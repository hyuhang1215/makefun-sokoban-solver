import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const chars = "UDLR";
type Board = { coords: [number,number][]; adj: number[][]; boxes: number[]; goals: number[]; player: number };
type State = { b: number[]; p: number; g:number; f:number; from:State|null; step:string; key:string };
export function parse(xsb:string):Board {
  const lines=xsb.replace(/\r/g,"").split("\n");
  const seen=new Map<string,number>(), coords:Board["coords"]=[], boxes:number[]=[],goals:number[]=[];
  let player=-1;
  for(let r=0;r<lines.length;r++) for(let c=0;c<lines[r].length;c++){
    const ch=lines[r][c]; if(!" .$*@+".includes(ch)) continue;
    const i=coords.length; coords.push([r,c]);seen.set(r+","+c,i);
    if("$*".includes(ch))boxes.push(i);
    if(".*+".includes(ch))goals.push(i);
    if("@+".includes(ch)){if(player>=0)throw Error("Multiple players");player=i;}
  }
  if(player<0||boxes.length!==goals.length)throw Error("Invalid level");
  const adj=coords.map(([r,c])=>[[r-1,c],[r+1,c],[r,c-1],[r,c+1]].map(([a,b])=>seen.get(a+","+b)??-1));
  return {coords,adj,boxes,goals,player};
}
const opposite=(d:number)=>d^1;
function reach(adj:number[][],p:number,b:Set<number>,paths=false){
  const seen=new Int32Array(adj.length).fill(-1), ds=paths?new Int8Array(adj.length):null;
  const q=[p];seen[p]=p;let anchor=p;
  for(let k=0;k<q.length;k++){
    const i=q[k]; if(i<anchor)anchor=i;
    for(let d=0;d<4;d++){const j=adj[i][d];if(j<0||seen[j]>=0||b.has(j))continue;
      q.push(j);seen[j]=i;if(ds)ds[j]=d;
    }
  }
  return {seen,anchor,path(j:number){if(!ds||seen[j]<0)throw Error("unreachable");let s="";while(j!==p){s=chars[ds[j]]+s;j=seen[j];}return s;}};
}
class Heap {
  a:State[]=[];
  static less(x:State,y:State){return x.f<y.f||(x.f===y.f&&x.g>y.g);}
  push(s:State){let i=this.a.length;this.a.push(s);while(i){const p=(i-1)>>1;if(!Heap.less(s,this.a[p]))break;this.a[i]=this.a[p];i=p;}this.a[i]=s;}
  pop(){const a=this.a, s=a[0], z=a.pop()!;if(a.length){let i=0;while(i*2+1<a.length){let j=i*2+1;if(j+1<a.length&&Heap.less(a[j+1],a[j]))j++;if(!Heap.less(a[j],z))break;a[i]=a[j];i=j;}a[i]=z;}return s;}
}
function solveRegion(adj:number[][],boxes:number[],goals:number[],p:number,budget:{left:number}):string|null {
  const goal=new Set(goals);
  const dis=goals.map(g=>{
    const a=new Int16Array(adj.length).fill(-1);a[g]=0;const q=[g];
    for(let k=0;k<q.length;k++){const x=q[k];for(let d=0;d<4;d++){
      const y=adj[x][d];if(y<0||a[y]>=0||adj[y][d]<0)continue;
      a[y]=a[x]+1;q.push(y);
    }}return a;
  });
  const memo=new Map<string,number>();
  function lower(bs:number[]){
    const key=bs.join(","), old=memo.get(key);if(old!==undefined)return old;
    let h:number;
    if(goals.length<=8){
      const dp=new Float64Array(1<<goals.length).fill(Infinity);dp[0]=0;
      for(let m=0;m<dp.length-1;m++){
        if(!Number.isFinite(dp[m]))continue;
        let n=m,i=0;while(n){n&=n-1;i++;}
        for(let j=0;j<goals.length;j++)if(!(m&(1<<j))&&dis[j][bs[i]]>=0){
          const t=m|(1<<j),v=dp[m]+dis[j][bs[i]];if(v<dp[t])dp[t]=v;
        }
      }
      h=dp[dp.length-1];
    }else{
      h=0;for(const b of bs){let v=Infinity;for(const d of dis)if(d[b]>=0&&d[b]<v)v=d[b];h+=v;}
    }
    memo.set(key,h);return h;
  }
  const h=lower(boxes);if(!Number.isFinite(h))return null;
  const key=boxes.join(",")+"|"+reach(adj,p,new Set(boxes)).anchor;
  const best=new Map([[key,0]]), heap=new Heap();
  heap.push({b:boxes,p,g:0,f:h,from:null,step:"",key});
  while(heap.a.length){
    if(--budget.left<0)return null;
    const s=heap.pop();if(best.get(s.key)!==s.g)continue;
    if(s.b.every(x=>goal.has(x))){
      const steps:string[]=[];for(let x:State|null=s;x;x=x.from)steps.push(x.step);
      return steps.reverse().join("");
    }
    const occ=new Set(s.b), r=reach(adj,s.p,occ,true), g=s.g+1;
    for(let i=0;i<s.b.length;i++){
      const b=s.b[i];
      for(let d=0;d<4;d++){
        const to=adj[b][d], behind=adj[b][opposite(d)];
        if(to<0||behind<0||occ.has(to)||r.seen[behind]<0)continue;
        const bs=s.b.slice();bs[i]=to;bs.sort((a,b)=>a-b);
        const h=lower(bs);if(!Number.isFinite(h))continue;
        const key=bs.join(",")+"|"+reach(adj,b,new Set(bs)).anchor;
        if((best.get(key)??Infinity)<=g)continue;
        best.set(key,g);heap.push({b:bs,p:b,g,f:g+h,from:s,step:r.path(behind)+chars[d],key});
      }
    }
  }
  return null;
}
export function replay(board:Board,moves:string,p=board.player,boxes=board.boxes){
  const b=new Set(boxes);let pushes=0;
  for(const ch of moves){
    const d=chars.indexOf(ch.toUpperCase());
    if(d<0)throw Error("bad move");
    const q=board.adj[p][d];
    if(q<0)throw Error("walked into wall");
    if(b.has(q)){
      const t=board.adj[q][d];if(t<0||b.has(t))throw Error("illegal push");
      b.delete(q);b.add(t);pushes++;
    }
    p=q;
  }
  return {p,boxes:[...b],pushes,solved:board.goals.every(x=>b.has(x))};
}
export function solve(board:Board,budget={left:60000}):string|null {
  const {adj,boxes,goals,coords,player}=board;
  const hallway=new Set(coords.flatMap(([r],i)=>r===coords[player][0]?[i]:[]));
  const assigned=new Set(hallway), rooms:{inside:Set<number>,anchor:number,bs:number[],gs:number[]}[]=[];
  let valid=boxes.every(x=>!hallway.has(x))&&goals.every(x=>!hallway.has(x));
  for(let start=0;start<adj.length&&valid;start++)if(!assigned.has(start)){
    const inside=new Set([start]), q=[start];assigned.add(start);
    const portal=new Set<string>();let anchor=-1,door=-1;
    for(let k=0;k<q.length;k++)for(const j of adj[q[k]])if(j>=0){
      if(hallway.has(j)){portal.add(q[k]+":"+j);anchor=j;door=q[k];}
      else if(!assigned.has(j)){assigned.add(j);inside.add(j);q.push(j);}
    }
    const bs=boxes.filter(i=>inside.has(i)), gs=goals.filter(i=>inside.has(i));
    if(!bs.length&&!gs.length)continue;
    // A box exiting into the hallway cannot be pushed back through a one-cell door.
    const outside=anchor<0?-1:adj[anchor][adj[door].indexOf(anchor)];
    if(portal.size!==1||outside>=0||bs.length!==gs.length||bs.length>4||inside.size>40){valid=false;break;}
    rooms.push({inside,anchor,bs,gs});
  }
  if(valid&&rooms.length&&rooms.reduce((n,r)=>n+r.bs.length,0)===boxes.length){
    let p=player, moves="", current=boxes;
    for(const {inside,anchor,bs,gs} of rooms){
      const subset=new Set([...inside,anchor]), indices=[...subset], lookup=new Map(indices.map((x,i)=>[x,i]));
      const sub=indices.map(i=>adj[i].map(j=>lookup.get(j)??-1));
      const plan=solveRegion(sub,bs.map(i=>lookup.get(i)!).sort((a,b)=>a-b),gs.map(i=>lookup.get(i)!),lookup.get(anchor)!,budget);
      if(plan===null){valid=false;break;}
      const travel=reach(adj,p,new Set(current),true);
      if(travel.seen[anchor]<0){valid=false;break;}
      const segment=travel.path(anchor)+plan, result=replay(board,segment,p,current);
      p=result.p;current=result.boxes;moves+=segment;
    }
    if(valid&&replay(board,moves).solved)return moves;
  }
  return solveRegion(adj,boxes,goals,player,budget);
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
  if(process.argv.length===3){
    const moves=solve(parse(readFileSync(process.argv[2],"utf8")));
    if(moves===null)process.exitCode=1;else console.log(moves);
  }else{
    const input=process.argv[2]??"/input", output=process.argv[3]??"/output";
    for(const id of readdirSync(input).sort()){
      const moves=solve(parse(readFileSync(join(input,id,"level.txt"),"utf8")));
      mkdirSync(join(output,id),{recursive:true});
      writeFileSync(join(output,id,"solution.txt"),(moves??"")+"\n");
    }
  }
}
