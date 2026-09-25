# scratch/ WIP 台账（K5，2026-09-12 登记）

依据：2026-09-08 改良建议 K5（P3）——「为 scratch 内每个含 sorry 的 WIP 文件
登记一行（文件名→目标模块→状态）；scratch 内禁止 axiom」。

## 政策

- `scratch/` 是 WIP 开发区：**允许 `sorry`**（开发中占位），**禁止 `axiom`**
  （`verify_build.ps1` 前置 axiom 扫描拦截，违者构建失败）。
- 正式模块 `CddFormalization/` 必须 0 sorry / 0 axiom（2026-09-08 审计：
  27/27 全绿、0 sorry、0 axiom，`axiom_audit_out.txt` 全部为标准三公理）。
- 防误入机制：`verify_build.ps1` 的 axiom 前置扫描 + 目录源文件计数自检；
  本台账为其人工对照层。

## 本轮扫描记录（2026-09-12）

- 扫描命令：`rg -n 'sorry|admit|sorryAx' H:\cdd_lean4\scratch`；
  `rg -n '^\s*axiom\b' H:\cdd_lean4\scratch`（0 命中）。
- 结果：28 个文件；`sorry` 共 **6 处**，集中于 3 个文件
  （`probe_weil` L72/77/80/89、`probe_weil3` L81、`scratch_agentC` L73）；
  `axiom` **0 处**。与 2026-09-08 审计记录逐条一致，期间无新增 WIP。

## 台账（文件名 → 目标模块 → 状态）

### RH_WeilFormula 线（节点 21 组装探针链）

| 文件 | 目标模块 | 状态 |
| -- | -- | -- |
| probe_weil.lean | RH_WeilFormula（测度论组装：probeMeasure 有限性 / Laplace 变换=级数 / n^(-s)=exp(-s·log n) / 零点非聚点） | **WIP，sorry×4**（L72/77/80/89） |
| probe_weil2.lean | RH_WeilFormula（SumMeasure+ZetaAsymp 探针） | 探针（无 sorry），服务已完成节点，可归档 |
| probe_weil3.lean | RH_WeilFormula（高阶零点 m_ρ 导数分解；Mathlib `HasDerivAt` API 不确定） | **WIP，sorry×1**（L81） |
| probe_weil4.lean | RH_WeilFormula（MellinInversion / Analytic.Uniqueness 探针） | 探针（无 sorry） |
| probe_weil5.lean | RH_WeilFormula（Analytic.Order + ZetaAsymp 探针） | 探针（无 sorry） |
| probe_weil6.lean | RH_WeilFormula（LSeries.ZetaZeros 探针） | 探针（无 sorry） |
| probe_weil7.lean | RH_WeilFormula（节点 21 开发中期探针） | 探针（无 sorry） |
| probe_weil8.lean | RH_WeilFormula（CircleIntegral / CauchyIntegral 探针） | 探针（无 sorry） |
| probe_weil9.lean | RH_WeilFormula（最小签名探针） | 探针（无 sorry） |
| probe_weil10.lean | RH_WeilFormula（节点 21 后期探针） | 探针（无 sorry） |
| TmpCheck.lean | RH_WeilFormula（K2 拆分前 FourierTransform 逐点展开试验） | 临时检查，可清理 |
| TmpCheck2.lean | RH_WeilFormula（`#check @Real.fourier_eq'` 签名核对） | 临时检查，可清理 |

### RH_ExplicitFormula / RH_DeviationMeasure 线

| 文件 | 目标模块 | 状态 |
| -- | -- | -- |
| probe_api.lean | RH_ExplicitFormula（节点 10：Chebyshev/LSeries/AbelSummation/MellinTransform API 探针） | 探针（无 sorry），节点已并入正式模块，可归档 |
| probe_api2.lean | RH_ExplicitFormula（节点 10：SumCoeff 变体探针） | 探针（无 sorry），可归档 |
| probe_api3.lean | RH_ExplicitFormula（节点 10：ImproperIntegrals 变体探针） | 探针（无 sorry），可归档 |
| probe_mellin.lean | RH_ExplicitFormula（节点 11 Mellin 桥冒烟测试；头注自记「已集成至主模块 §6」） | 已完成，可归档 |
| probe_dev.lean | RH_DeviationMeasure（节点 12-14 偏差测度：FiniteMeasure 归一化展开探针） | 开发草稿（无 sorry） |

### RH_LiCriterion 线（辐角回归 / 多维同时回归）

| 文件 | 目标模块 | 状态 |
| -- | -- | -- |
| probe_sig.lean | RH_LiCriterion（Dirichlet 逼近 / Arg / Trigonometric.Bounds API 探针） | 探针（无 sorry） |
| probe_sig2.lean | RH_LiCriterion（同上，签名变体） | 探针（无 sorry） |
| scratch_agentB.lean | RH_LiCriterion（agentB 分工草稿：无理辐角回归路径） | 草稿（无 sorry） |
| scratch_agentC.lean | RH_LiCriterion（agentC 分工草稿：有理辐角回归；`exists_ge_cos_ge`） | **WIP，sorry×1**（L73） |
| scratch_dom.lean | RH_LiCriterion（2026-09-04 H3 fix：占位 axiom `exists_simultaneous_cos_ge` 已删除，本体收编为正式定理 `RH_LiCriterion.lean:478`） | 已收编正式模块，保留作回归参考 |
| scratch_sim.lean | RH_LiCriterion（多维同时辐角回归：鸽笼 Dirichlet + 倍增模拟） | 草稿（无 sorry） |
| scratch_test.lean | RH_LiCriterion 基础层（Pigeonhole / Floor / Arg 测试） | 测试（无 sorry） |
| scratch_test2.lean | RH_LiCriterion 基础层（Pigeonhole / Floor 测试） | 测试（无 sorry） |

### 基础回归

| 文件 | 目标模块 | 状态 |
| -- | -- | -- |
| TestRat.lean | Mathlib Rat 验证链回归测试（Lean 4.32.2；头注自记历史说明） | 回归测试，保留 |

## sorry 明细（唯一未收编内容，共 6 处）

| 位置 | 声明 | 阻塞点 |
| -- | -- | -- |
| probe_weil.lean:72 | `probeMeasure (Set.Iic T) < ∞` | vonMangoldt 加权 Dirac 和测度的有限性 |
| probe_weil.lean:77 | `∫ exp(-s·x) ∂probeMeasure = ∑' Λ(n) • exp(-s·log n)` | Measure.sum 与 cntbl 测度的积分-级数交换 |
| probe_weil.lean:80 | `(n : ℂ) ^ (-s) = exp(-s · log n)` | ℂ 幂-指数转换的 API 形式 |
| probe_weil.lean:89 | `¬ ∀ᶠ z ∈ 𝓝 ρ, riemannZeta z = 0` | 非平凡零点非恒零邻域（零点孤立性） |
| probe_weil3.lean:81 | 高阶零点 `ζ' = m(s-ρ)^{m-1}g + (s-ρ)^m g'` | `AnalyticOn` → `HasDerivAt` eventual 绑定 API 不确定 |
| scratch_agentC.lean:73 | `exists_ge_cos_ge`（有理情形余弦回归） | 已被正式模块 `exists_simultaneous_cos_ge` 覆盖更一般情形，本 sorry 属分工草稿残留 |

> 注：probe_weil 系列的 4 处 sorry 属于测度论组装路径的早期探针，正式模块
> `RH_WeilFormula.lean` 节点 21 已按 K2 拆分（2026-09-08）以具名假设
> `hadamard_gap_hypothesis` 处理组装，不再依赖这些探针结论；探针仅保留
> 供未来 Mathlib API 补齐后回填。

## 变更纪律

- 新增 WIP 文件须在本台账登记（文件名→目标模块→状态）。
- sorry 收编正式模块后，将对应行状态改为「已收编」并注明正式定理位置。
- scratch 内出现 `axiom` 属违纪，须立即删除或收编（先例：scratch_dom.lean
  的 H3 fix，2026-09-04）。
