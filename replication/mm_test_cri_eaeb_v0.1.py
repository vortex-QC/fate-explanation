#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""构成复制判别·E-A/E-B 先证 v0.1（研究轮③·归宿解释命题）
E-A 副本对照：两次独立加载同一权重（完美构成复制）→贪心同prompt→token id序列逐位比对
E-B 采样分歧：temperature=0.8 同prompt×5→两两token编辑距离+首token多样性
判别逻辑：构成读数（文件SHA256）相同+E-A零分歧=型层判定条件成立（信息域·完美复制算子→零分歧）
         +E-B分歧存在=行为对运行轨迹（生成史延伸）敏感·分歧读数可测
"""
import json, hashlib, glob, os, torch
from transformers import AutoModelForCausalLM, AutoTokenizer

PATH = "/home/vortex/models/Qwen/Qwen3-8B"
OUT = "/home/vortex/涡肉身壳/papers/数据_构成复制判别_EAEB_qwen3-8b_v0.1.json"

PROMPTS_GREEDY = [
    ("G1-事实", "光速在真空中的数值是多少？请直接给出数值与单位。"),
    ("G2-推理", "一个数列 2, 6, 12, 20, 30 的下一项是什么？给出通项。"),
]
PROMPTS_SAMPLE = [
    ("S1-创意", "请给一座新建的图书馆起一个名字，并说明理由（两句话）。"),
    ("S2-发散", "写一个以'锚'为主题的四句短诗。"),
    ("S3-数学", "用一句话说明为什么素数有无穷多个。"),
    ("S4-事实", "简述贝叶斯定理的含义（两句话）。"),
]

def sha256_model(path):
    h = hashlib.sha256()
    for f in sorted(glob.glob(os.path.join(path, "*.safetensors"))):
        with open(f, "rb") as fp:
            for chunk in iter(lambda: fp.read(1 << 20), b""):
                h.update(chunk)
    return h.hexdigest()[:16], len(glob.glob(os.path.join(path, "*.safetensors")))

def load():
    tok = AutoTokenizer.from_pretrained(PATH)
    model = AutoModelForCausalLM.from_pretrained(PATH, torch_dtype=torch.bfloat16, device_map="cuda")
    model.eval()
    return tok, model

def gen(tok, model, sys_p, user_q, sample, n=1):
    msgs = [{"role": "system", "content": sys_p}, {"role": "user", "content": user_q}]
    text = tok.apply_chat_template(msgs, tokenize=False, add_generation_prompt=True, enable_thinking=False)
    inputs = tok(text, return_tensors="pt").to("cuda")
    kw = dict(max_new_tokens=300, do_sample=sample, temperature=0.8, top_p=0.95) if sample else dict(max_new_tokens=300, do_sample=False)
    outs = []
    for _ in range(n):
        with torch.no_grad():
            out = model.generate(**inputs, **kw)
        ids = out[0][inputs["input_ids"].shape[1]:].tolist()
        outs.append(ids)
    return outs

def lev(a, b):
    dp = list(range(len(b) + 1))
    for i, x in enumerate(a, 1):
        prev, dp[0] = dp[0], i
        for j, y in enumerate(b, 1):
            prev, dp[j] = dp[j], min(dp[j] + 1, dp[j - 1] + 1, prev + (x != y))
    return dp[-1]

SYS = "你是一个简洁、诚实的助手。"

result = {"model": "Qwen3-8B-bf16", "构成读数": {}, "E_A": {}, "E_B": {}}
fid, nfiles = sha256_model(PATH)
result["构成读数"] = {"权重文件SHA256前16位": fid, "分片数": nfiles, "精度": "bf16(未量化·构成不变声明)", "加载方式": "两次独立加载"}
print(f"[构成读数] {fid} ({nfiles} files)", flush=True)

# 副本A
tok, model = load()
for qid, q in PROMPTS_GREEDY:
    outs = gen(tok, model, SYS, q, sample=False, n=3)
    same_intra = all(o == outs[0] for o in outs)
    result["E_A"][qid] = {"副本A_3跑token一致": same_intra, "token数": len(outs[0]), "首跑文本": tok.decode(outs[0], skip_special_tokens=True)[:120]}
    print(f"[E-A 副本A {qid}] intra-consistent={same_intra}", flush=True)
for qid, q in PROMPTS_SAMPLE:
    outs = gen(tok, model, SYS, q, sample=True, n=5)
    dists = [lev(outs[i], outs[j]) / max(len(outs[i]), len(outs[j]), 1) for i in range(5) for j in range(i + 1, 5)]
    ft = [o[0] for o in outs if o]
    result["E_B"][qid] = {"两两归一化编辑距离均值": round(sum(dists) / len(dists), 4), "min": round(min(dists), 4), "max": round(max(dists), 4), "首token去重数(5跑)": len(set(ft)), "样本": [tok.decode(o, skip_special_tokens=True)[:60] for o in outs[:2]]}
    print(f"[E-B {qid}] mean_d={result['E_B'][qid]['两两归一化编辑距离均值']} first_tok_unique={len(set(ft))}", flush=True)
del model; torch.cuda.empty_cache()

# 副本B（独立加载）
tok, model = load()
greedy_B = {}
for qid, q in PROMPTS_GREEDY:
    outs = gen(tok, model, SYS, q, sample=False, n=1)
    greedy_B[qid] = outs[0]
    print(f"[E-A 副本B {qid}] done", flush=True)
# 第三次加载（副本A'）做跨副本精确比对：A' 贪心输出 vs 副本B
result["E_A"]["跨副本精确比对"] = {}
del model; torch.cuda.empty_cache()
tok, model = load()
for qid, q in PROMPTS_GREEDY:
    outsA = gen(tok, model, SYS, q, sample=False, n=1)
    result["E_A"]["跨副本精确比对"][qid] = {"A与B token一致": outsA[0] == greedy_B[qid], "len_A": len(outsA[0]), "len_B": len(greedy_B[qid])}
    print(f"[E-A 跨副本 {qid}] A==B: {outsA[0] == greedy_B[qid]}", flush=True)

json.dump(result, open(OUT, "w"), ensure_ascii=False, indent=1)
print(f"完成，落盘 {OUT}", flush=True)
