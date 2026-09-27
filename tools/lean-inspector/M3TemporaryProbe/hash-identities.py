import json,pathlib,sys,hashlib
p=pathlib.Path(sys.argv[1]); rows=json.loads(p.read_text()); nodes=0; total=0
for row in rows:
 for field in ['type_dag','value_dag']:
  raw=row.pop(field); value=None if raw is None else json.dumps(raw,sort_keys=True,separators=(',',':')).encode(); total+=len(value or b'');nodes+=len(raw['nodes']) if raw else 0
  row[field+'_sha256']=None if value is None else hashlib.sha256(value).hexdigest()
target=p.with_name(p.name.replace('.raw.json','.json'));target.write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'declarations':len(rows),'dag_nodes_including_per_declaration_duplicates':nodes,'serialized_bytes':total,'identities':str(target)}))
