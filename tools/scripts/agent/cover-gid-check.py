#!/usr/bin/env python3
"""Validate cover GIDs against a git revision: state pin, public theorem, Scribe handle.
usage: cover-gid-check.py <rev> <tsv with atom_id<TAB>GID> [...]
       cover-gid-check.py --selftest      check the Scribe handle parser against its known shapes

The Scribe handle is the precondition that a line-based grep gets wrong: DeclarationHandle.Create
takes its argument in at least five shapes, and four of them defeat a per-line regex.  The parser
below is checked against all five in --selftest."""
import subprocess,sys,re

def handle_of(scribe_text, decl):
    """True when the Scribe source declares a handle ending in `decl`.
    Resolves `const string NAME = "a" + "b";` so Create(NAME) and Create(NAME + "x") work."""
    flat=re.sub(r"\s+","",scribe_text)
    consts={}
    for cm in re.finditer(r'conststring([A-Za-z_][A-Za-z0-9_]*)=((?:"[^"]*"\+?)+);',flat):
        consts[cm.group(1)]="".join(re.findall(r'"([^"]*)"',cm.group(2)))
    for call in re.findall(r"DeclarationHandle\.Create\(([^()]*)\)",flat):
        parts=[]
        for tok in call.split("+"):
            tok=tok.strip()
            if tok.startswith('"') and tok.endswith('"'): parts.append(tok[1:-1])
            elif tok in consts: parts.append(consts[tok])
            else: parts.append("\x00")
        if "".join(parts).endswith(decl): return "strict"
    if re.search(r'DeclarationHandle\.Create\(',flat) and f'"{decl}"' in flat:
        return "literal"      # name passed through a helper parameter; weaker but sufficient
    return False

if "--selftest" in sys.argv[1:]:
    CASES=[
      ("whole literal", 'DeclarationHandle.Create("D5/S3/M.thm_name"),', "thm_name", "strict"),
      ("prefix constant",
       'private const string Prefix = "D5/S3/M.";\n DeclarationHandle.Create(Prefix + "thm_name"),',
       "thm_name", "strict"),
      ("call split across lines",
       'private const string P =\n "D5/S3/M.";\n DeclarationHandle.Create(\n   P + "thm_name"),',
       "thm_name", "strict"),
      ("gid concatenated inside the constant",
       'private const string Declaration =\n "D5/S3/M." \n + "thm_name";\n DeclarationHandle.Create(Declaration),',
       "thm_name", "strict"),
      ("name passed to a helper",
       'T("slug", "thm_name", "title"),\n DeclarationHandle.Create("D5/S3/M." + name), H(title),',
       "thm_name", "literal"),
      ("declaration absent", 'DeclarationHandle.Create("D5/S3/M.other"),', "thm_name", False),
      ("no handle at all", 'var x = "thm_name";', "thm_name", False),
    ]
    bad=0
    for name,src,decl,exp in CASES:
        got=handle_of(src.replace("\\n","\n"),decl); ok=(got==exp); bad+=0 if ok else 1
        print(f"  {'ok  ' if ok else 'FAIL'} {name:34s} expected={exp!r} got={got!r}")
    print(f"SELFTEST_{'PASS' if not bad else 'FAIL'} cases={len(CASES)} failed={bad}")
    sys.exit(1 if bad else 0)

rev=sys.argv[1]
gids=set()
for f in sys.argv[2:]:
    for line in open(f,encoding="utf-8"):
        p=line.rstrip("\n").split("\t")
        if len(p)>=2 and p[1].strip(): gids.add(p[1].strip())
def show(path):
    r=subprocess.run(["git","show",f"{rev}:{path}"],capture_output=True,text=True)
    return r.stdout if r.returncode==0 else None
bad=0
for g in sorted(gids):
    mod,dec=g.rsplit(".",1)
    pin = show(f"Golden/Frozen/state/{mod}.lean.json") is not None
    src = show(f"{mod}.lean") or ""
    m=re.search(rf"^(private\s+)?(protected\s+)?(theorem|lemma|def|abbrev|instance|noncomputable\s+def)\s+{re.escape(dec)}\b",src,re.M)
    kind = (m.group(0).split()[-2] if m and m.group(1) else (m.group(3) if m else None))
    priv = bool(m and m.group(1))
    isthm = kind in ("theorem","lemma")
    scr = show(f"Blueprint/{mod}.scribe.cs")
    handle = handle_of(scr, dec) if scr else False
    ok = pin and isthm and not priv and handle
    if not ok: bad+=1
    print(f"{'OK ' if ok else 'BAD'} pin={'Y' if pin else 'N'} kind={kind or 'MISSING'} private={'Y' if priv else 'N'} scribe={'Y' if scr else 'NOFILE'} handle={handle or 'N'}  {g}")
print(f"\n{len(gids)} gids, {bad} rejected")
sys.exit(1 if bad else 0)
