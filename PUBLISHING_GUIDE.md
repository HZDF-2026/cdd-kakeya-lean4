# CDD Kakeya Lean4 — 多平台发布指南

> 本文件记录项目在各平台的发布状态和操作指南。

## 已完成

### GitHub (主仓库) ✅

- **仓库地址**: https://github.com/HZDF-2026/cdd-kakeya-lean4
- **状态**: 已推送 (main 分支)
- **内容**: 完整项目代码 (Kakeya.lean v7, Basic.lean, README.md, LICENSE, lakefile.toml, lean-toolchain)
- **待办**: CI workflow 文件需手动添加 (因 token 缺少 workflow scope)

#### 手动添加 CI 文件

在 GitHub 网页操作:
1. 打开 https://github.com/HZDF-2026/cdd-kakeya-lean4
2. 点击 "Add file" → "Create new file"
3. 文件名: `.github/workflows/lean_action_ci.yml`
4. 内容:

```yaml
name: Lean Action CI

on:
  push:
  pull_request:
  workflow_dispatch:

jobs:
  build:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
```

5. 点击 "Commit new file"

## 待发布

### Gitee (国内镜像)

**操作步骤**:

1. 访问 https://gitee.com 并注册/登录
2. 点击右上角 "+" → "新建仓库"
3. 仓库名称: `cdd-kakeya-lean4`
4. 选择 "开源"，添加许可证 Apache-2.0
5. 点击 "创建"

**推送代码**:

```powershell
$env:Path = 'H:\MinGit\cmd;' + $env:Path
cd H:\cdd_lean4

# 添加 Gitee 远程
git remote add gitee https://gitee.com/你的用户名/cdd-kakeya-lean4.git

# 推送到 Gitee
git push -u gitee main
```

**或使用 Gitee 导入功能**:
1. 访问 https://gitee.com/repo/create
2. 选择 "导入已有仓库"
3. 输入 GitHub 仓库 URL: https://github.com/HZDF-2026/cdd-kakeya-lean4
4. 点击 "导入"

### ChinaXiv (国内学术预印本)

**操作步骤**:

1. 访问 https://chinaxiv.org 并注册
2. 选择 "论文预印本" → "提交预印本"
3. 学科分类: 物理学 / 数学
4. 填写信息:
   - 标题: CDD 挂谷猜想谱化解的 Lean 4 条件等价性形式化验证
   - 摘要: 使用纯 Lean 4 标准库（无 Mathlib 依赖）对 CDD 理论框架中的挂谷猜想谱化解进行条件等价性形式化验证。项目包含 14 个定义、29 个定理和 1 个 example，通过 24 项 verification_summary 覆盖全部核心定理，经六轮学术审稿达到 A 级评级。
   - 关键词: 挂谷猜想, Lean 4, 形式化验证, 谱测度分解, Hausdorff 维数
5. 上传附件: README.md 转为 PDF，或直接上传源代码 zip
6. 提交审核

**注意**: ChinaXiv 主要面向学术论文预印本。若仅有代码项目，建议:
- 撰写一份研究说明文档 (PDF)，描述理论框架和形式化验证结果
- 将代码作为 supplementary material 上传

### Zenodo (国际学术归档 + DOI)

**操作步骤**:

1. 访问 https://zenodo.org 并用 GitHub 账号登录
2. 点击 "New upload"
3. 填写信息:
   - Resource type: Software
   - Title: CDD Kakeya Conjecture Spectral Resolution: Lean 4 Formalization
   - Authors: [你的名字]
   - Description: 项目描述 (可从 README 复制)
   - License: Apache-2.0 (源代码) + CC BY-NC 4.0 (文档)
4. 上传文件: 将 H:\cdd_lean4 打包为 zip 上传
5. 点击 "Publish"
6. 获取 DOI (如 10.5281/zenodo.xxxxxxx)

**或使用 GitHub-Zenodo 集成** (推荐):
1. 访问 https://zenodo.org/account/settings/github/
2. 找到 `HZDF-2026/cdd-kakeya-lean4` 仓库并开启
3. 在 GitHub 上创建一个 Release (如 v7.0)
4. Zenodo 会自动归档并分配 DOI

### GitLab (备选国际平台)

**操作步骤**:

1. 访问 https://gitlab.com 并注册/登录
2. 点击 "New project" → "Import project" → "GitHub"
3. 选择 `cdd-kakeya-lean4` 仓库导入
4. 或手动推送:
```powershell
git remote add gitlab https://gitlab.com/你的用户名/cdd-kakeya-lean4.git
git push -u gitlab main
```

### Codeberg (非营利开源平台)

**操作步骤**:

1. 访问 https://codeberg.org 并注册
2. 创建新仓库
3. 推送代码:
```powershell
git remote add codeberg https://codeberg.org/你的用户名/cdd-kakeya-lean4.git
git push -u codeberg main
```

## 发布状态汇总

| 平台 | 类型 | 状态 | 门槛 |
|------|------|------|------|
| GitHub | 代码托管 | ✅ 已发布 | 注册即可 |
| Gitee | 代码托管 | 待发布 | 注册即可 |
| GitLab | 代码托管 | 待发布 | 注册即可 |
| Codeberg | 代码托管 | 待发布 | 注册即可 |
| Zenodo | 学术归档 | 待发布 | 注册即可, 可获 DOI |
| ChinaXiv | 预印本 | 待发布 | 注册即可 |

## 引用格式

发布后可用以下格式引用:

```bibtex
@misc{cdd_kakeya_lean4,
  title={CDD Kakeya Conjecture Spectral Resolution: Lean 4 Conditional Equivalence Formalization},
  author={HZDF-2026},
  year={2026},
  howpublished={\url{https://github.com/HZDF-2026/cdd-kakeya-lean4}},
  note={Lean 4 formalization, 0 sorry, pure core (no Mathlib), A-rated through 6 rounds of peer review}
}
```
