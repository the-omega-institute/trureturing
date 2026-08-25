import glob,sys,xml.etree.ElementTree as ET,collections
ns={'t':'http://microsoft.com/schemas/VisualStudio/TeamTest/2010'}
rows=[]
for f in glob.glob('**/TestResults/*.trx',recursive=True)+glob.glob('**/*.trx',recursive=True):
    try: r=ET.parse(f).getroot()
    except Exception: continue
    for u in r.findall('.//t:UnitTestResult',ns):
        d=u.get('duration') or '0:0:0'
        try:
            h,m,s=d.split(':'); sec=int(h)*3600+int(m)*60+float(s)
        except Exception: sec=0.0
        rows.append((sec,u.get('testName',''),f))
if not rows:
    print('TIMING_PROBE no trx rows found'); sys.exit(0)
rows.sort(reverse=True)
tot=sum(r[0] for r in rows)
print('TIMING_PROBE total_tests=%d sum_seconds=%.1f'%(len(rows),tot))
print('TIMING_PROBE top60:')
for sec,name,f in rows[:60]:
    print('TIMING_ROW %8.2f  %s'%(sec,name[:150]))
cls=collections.Counter()
for sec,name,f in rows:
    cls[name.rsplit('.',1)[0] if '.' in name else name]+=sec
print('TIMING_PROBE top30_classes:')
for k,v in cls.most_common(30):
    print('TIMING_CLASS %8.2f  %s'%(v,k[:150]))
