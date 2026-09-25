import json
d = json.load(open('H:/cdd_p5_v28_4_results.json', encoding='utf-8'))
print('== _meta ==')
print(json.dumps(d['_meta'], ensure_ascii=False, indent=1)[:1200])
print('== D_v6d_synthesis keys ==')
print(list(d['D_v6d_synthesis'].keys()))
ds = d['D_v6d_synthesis']
print(json.dumps(ds, ensure_ascii=False, indent=1)[:2000])
