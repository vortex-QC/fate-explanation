/-
# 归宿解释命题·形式核 (T_F1-T_F8, 2026-10-07)
对应: papers/归宿解释命题_立项_v0.1.md (三钉全落 §二a/b/c) + 研究轮②③④⑤ (先例一手核验/
  构成复制判别实验设计/谱系vs因果辨析/谱系表扩充·2026-10-07)
体系: 主人命题"没有第一性解释, 只有归宿, 或者说归宿就是解释" (2026-10-06 观察起源逐字锚定);
  钉-1 互补面 (终点读法=投影面/谱系读法=完备面·接口=纤维测度结构·主人实数轴论证);
  钉-2 域索引排他性 (物理域排他/信息数学域不排他·排他性是域的函数);
  钉-3 分层判据 (可复制域=定义性判据·历史唯一域=构造数学推导·命题定位=现象描述层).

层位: 静=显化定理 (StaticCore/22785052) 与锚数 3.12 (锚=生成史的签名·22866459) 之上 ——
  解释论维的形式化: π:H→X 显化映射, 终点读法=过 π 因式化的解释函数, 谱系读法=直接读 H.

语义锚 (体系层·不进形式层):
  - H 生成史空间=动 (D0 自发动力学对象), X 显化态空间=静 (静=显化);
  - genidentity (Lewin 1922·Carnap Aufbau 采纳): 同一性由生成连接构成——≡_o 定义域在 H 的
    概念先例 (同构度第二先例·仅次物种个体论 Ghiselin/Hull);
  - 构成复制判别 (三面读数框架: 构成面/运行史面/训练史面·研究轮③): E-A 跨副本贪心逐 token
    全同 (完美复制算子模型域可执行实证) / E-B 采样分歧度分层 (运行史面分歧可测);
  - 混沌论证 (辨析档区别 3): 因果律完备不消除 π 纤维欠定——因果解释与谱系解释正交 (非粗细版).

边界 (如实标): 纤维测度结构=集合论离散模拟 (单点纤维/多点纤维二分·真测度版候后续);
  "分辨率-欠定度单调" (钉-1 成本权衡) 是连续概念不在本核; 复制必损=公理面假设 (物理机理
  三件套: 不可克隆+不可逆+混沌——机理本身不在本核); 翻译层纪律: 定理级=抽象结构内.
-/
import Mathlib

namespace FateExplanation

/-! ## 零、基本设置 -/

variable {H X : Type*} (π : H → X)

/-! ## 一、欠定引理与终点读法的界 (钉-1 互补面·形式对应) -/

/-- T_F1 欠定引理 (存在性形式): π 非单射 ⟹ 存在多点纤维 —— 显化态 x 处
    至少有两个不同生成史显化为它 (静欠定的代数面). -/
theorem existsMultiFiber (hπ : ¬ Function.Injective π) :
    ∃ x : X, ∃ h₁ h₂ : H, h₁ ≠ h₂ ∧ π h₁ = x ∧ π h₂ = x := by
  rw [Function.Injective] at hπ
  push_neg at hπ
  obtain ⟨h₁, h₂, hsame, hne⟩ := hπ
  exact ⟨π h₂, h₁, h₂, hne, hsame, rfl⟩

/-- 解释函数依赖 X (终点读法) 的形式定义: 过 π 因式化 —— 读数只看显化态. -/
def FactorsThrough (π : H → X) (e : H → β) : Prop := ∃ g : X → β, ∀ h, e h = g (π h)

/-- T_F2 例外欠定性: 同纤维两点上, 任何终点读法 (X 因式化函数) 取同值 ——
    终点读法原则上无法区分同显化的不同生成史. -/
theorem undetermined (e : H → β) (he : FactorsThrough π e) {h₁ h₂ : H}
    (hsame : π h₁ = π h₂) : e h₁ = e h₂ := by
  obtain ⟨g, hg⟩ := he
  rw [hg h₁, hg h₂, hsame]

/-- T_F3 升谱系的形式: 同纤维不同史的两点 —— 终点读法同值而 H 恒等读数分离
    (个体同一性在此处只能由 H 读出). -/
theorem lineageRescues {h₁ h₂ : H} (hsame : π h₁ = π h₂) (hne : h₁ ≠ h₂)
    (e : H → β) (he : FactorsThrough π e) :
    e h₁ = e h₂ ∧ h₁ ≠ h₂ :=
  ⟨undetermined π e he hsame, hne⟩

/-- T_F4 终点读法完备性二分 (一般位置充分/例外位置欠定·钉-1 互补面):
    π 单射 ⟺ 存在从 X 重构 H 的读法 (终点读法在一般位置=全域单点上充分). -/
theorem endpoint_bipartite [Nonempty H] [Nonempty X] :
    Function.Injective π ↔ ∃ g : X → H, ∀ h, g (π h) = h := by
  constructor
  · intro hi
    exact ⟨Function.invFun π, fun h => Function.leftInverse_invFun hi h⟩
  · rintro ⟨g, hg⟩ h₁ h₂ hsame
    calc h₁ = g (π h₁) := (hg h₁).symm
      _ = g (π h₂) := by rw [hsame]
      _ = h₂ := hg h₂

/-! ## 二、动本体定义与谱系解释必要性 (个体分辨·核心定理) -/

/-- 生成同一性 (genidentity·Lewin 1922 对应件): 个体同一性关系定义在生成史空间 H 上,
    最小要求=自反 —— 严格细于纤维相等与否由分离前提逐点给出 (不预设). -/
def GenIdentity (rel : H → H → Prop) : Prop := ∀ h : H, rel h h

/-- T_F5 谱系解释必要性 (核心定理): 个体同一性关系 rel 在某同纤维对上分离 ⟹
    任何终点读法 (X 因式化解释函数) 遗漏该分离 —— 仅依赖 X 的解释函数
    不能穷尽定义在 H 上的个体性 —— 充分解释必须含 H 坐标 (归宿). -/
theorem genealogyNecessary (rel : H → H → Prop)
    (hsep : ∃ h₁ h₂ : H, π h₁ = π h₂ ∧ ¬ rel h₁ h₂)
    (e : H → β) (he : FactorsThrough π e) :
    ∃ h₁ h₂ : H, ¬ rel h₁ h₂ ∧ e h₁ = e h₂ := by
  obtain ⟨h₁, h₂, hsame, hrel⟩ := hsep
  exact ⟨h₁, h₂, hrel, undetermined π e he hsame⟩

/-! ## 三、域分层定理 (钉-2·排他性是域的函数) -/

section Domain

variable {D : Type*} {α β : Type*} (κ : D → α) (ρ : D → β)

/-- 型本体 (信息域/经典数学域读法): 个体同一性由构成读数决定 —— 构成同即同一. -/
def TypeIdentity : Prop := ∀ o o' : D, κ o = κ o' → o = o'

/-- 分歧对 (构成全同而行为分歧) —— 排他性 E(D) 的存在性读数 (判别判据·钉-3). -/
def DivergentPair : Prop := ∃ o o' : D, κ o = κ o' ∧ ρ o ≠ ρ o'

/-- 动本体对象 (判据级定义): 存在另一对象, 构成全同而行为分歧. -/
def DynamicOntic (o : D) : Prop := ∃ o' : D, κ o' = κ o ∧ ρ o' ≠ ρ o

/-- T_F6 型本体方向 (信息/经典数学域·¬E(D)): 个体=型 ⟹ 无分歧对 ——
    构成性解释在该域充分 (构成同即同一即行为同). -/
theorem typeIdentity_noDivergence (hT : TypeIdentity κ) : ¬ DivergentPair κ ρ := by
  rintro ⟨o, o', hk, hr⟩
  exact hr (congrArg ρ (hT o o' hk))

/-- 复制必损 (物理域公理面·机理三件套的抽象): 任何非恒等构成保持映射产生行为分歧. -/
def CopyIsLossy : Prop :=
  ∀ C : D → D, (∀ o, κ (C o) = κ o) → C ≠ id → ∃ o : D, ρ (C o) ≠ ρ o

/-- T_F7 物理域方向 (E(D)): 存在非恒等构成保持复制算子 + 复制必损 ⟹
    分歧对存在 —— 构成全同不蕴含个体同一, 构成性解释不充分 (排他成立). -/
theorem divergenceOfLossyCopy (hC : ∃ C : D → D, (∀ o, κ (C o) = κ o) ∧ C ≠ id)
    (hlossy : CopyIsLossy κ ρ) : DivergentPair κ ρ := by
  obtain ⟨C, hκ, hne⟩ := hC
  obtain ⟨o, hr⟩ := hlossy C hκ hne
  exact ⟨o, C o, (hκ o).symm, hr.symm⟩

/-- T_F8 动本体判据 (存在性件): 分歧对存在 ⟹ 存在动本体对象
    (构成复制判别的判定规则·钉-3 第一层"实验说话"的形式对应). -/
theorem dynamicOntic_of_pair (hD : DivergentPair κ ρ) : ∃ o : D, DynamicOntic κ ρ o := by
  obtain ⟨o, o', hk, hr⟩ := hD
  exact ⟨o, o', hk.symm, hr.symm⟩

end Domain

end FateExplanation

/-! ## 附: 轴检验 (发布物附录 A 引用格式)
#print axioms FateExplanation.existsMultiFiber     -- 预期: [Classical.choice, Quot.sound, propext]
#print axioms FateExplanation.genealogyNecessary   -- 同上·零 sorryAx
#print axioms FateExplanation.divergenceOfLossyCopy -- 同上·零 sorryAx
-/

