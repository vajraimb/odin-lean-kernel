import subprocess,os,sys,time,resource,json,glob
K=sys.argv[1]; T=int(sys.argv[2]) if len(sys.argv)>2 else 120
import re
res=[]
def tmo(f):
    base=os.path.basename(f)[:-7]
    for y in glob.glob(f"/tmp/lka/tests/**/{base}.yaml",recursive=True):
        m=re.search(r"^timeout:\s*(\d+)",open(y).read(),re.M)
        if m: return min(int(m.group(1)),T)
    return T
for exp in ("good","bad"):
    for f in sorted(glob.glob(f"{exp}/**/*.ndjson", recursive=True)):
        t=time.time()
        r0=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        try:
            p=subprocess.run(f"ulimit -s unlimited; ulimit -v 7000000; {K} {f}",shell=True,capture_output=True,timeout=tmo(f),text=True)
            rc=p.returncode; out=p.stdout
        except subprocess.TimeoutExpired:
            rc="timeout"; out=""
        dt=time.time()-t
        if rc==0: got="accept"
        elif rc==1: got="reject"
        elif rc=="timeout": got="timeout"
        else: got="crash"
        fails=[l for l in out.splitlines() if l.startswith("FAIL")][:1]
        res.append(dict(name=f,exp=exp,rc=rc,got=got,t=round(dt,2),fail=(fails[0][:160] if fails else "")))
json.dump(res,open("results.json","w"),indent=1)
from collections import Counter
c=Counter((r["exp"],r["got"]) for r in res)
for k,v in sorted(c.items()): print(k,v)
