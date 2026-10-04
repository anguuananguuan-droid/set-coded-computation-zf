# Isabelle/ZF 图灵机与 EPQ：审查和推进路线

审查日期：2026-09-07；实现进展更新：2026-10-04。审查基线：`6fb8e25b5010c3019f7c9a4f518e15a64b8e7161`。
审查开始时，本地 HEAD 与当时查询的 GitHub `main` 相同，工作区无未提交改动。
下文第 1—10 节保留九月审查与实现记录；最新进展见第 11 节，当前公开入口见仓库 README。

## 1. 判断

现有项目应保留，但不能按原路线直接宣告完成。它已有真实的集合编码机器语义、编码、数值求值、原始递归证书和自输入停机不可判定证明。最重要的缺陷在数值输出接口：旧版把有限列表的字面相等当成了无限空白纸带的内容相等，使任何会缩短一元输出的函数都无法实现。

这次先修复这一点，保留原有 `machine`、`update`、`step`、`steps` 和停机定义，并重新检查依赖输出接口的归约证明。没有修改 `AI_USAGE.md` 或 EPQ 原稿；旧 RV 保留为历史记录，不能替代本次审查。

用户已明确目标：在 Isabelle/ZF 中构建标准图灵机，并连接 EPQ 的最终结论。本文中的后续路线是据此提出的实现方向；未完成的部分均明确列为开放义务。

## 2. 审查范围与证据边界

已通读仓库中的 EPQ 八页正文与参考文献，视觉核对第 V 节核心归约页；审查全部十二个原有 theory 的定义、主要结论和依赖，重点核对输出、停机、默认指令、对角化解释、顺序交接及 CH locale。阅读 README、Module III 技术说明和三个历史 RV，核对 ROOT/ROOTS、忽略规则和 GitHub 版本。补读本地 EPQ LaTeX 的核心论证、早期恢复计划及 ITP 研究摘要；后两者描述旧接口，不能作为当前完成状态。`Mechanical_Mathematics` 的文档属于另一个整本 Jech 形式化架构设想，不作为本次图灵机工作的依赖。私人自述与对话档案未纳入内容审查。

形式证明的有效性以 Isabelle 构建为准；语义是否表达目标另行审查。构建通过不会证明一个不恰当的定义恰当。本报告不把旧 RV 的“独立审查通过”当成这次独立复核的证据，也不声称逐行重做了所有长算术证明或从原始文献重新证明了 EPQ 引用的全部集合论结果。

## 3. 必须修复的输出缺陷

基线 `Turing_Reduction.thy` 要求：

```text
steps(M, initial_config(numeral_input(n)), k)
  = <0, <[], numeral_input(m)>>
```

令 `tape_span(t) = length(fst(t)) + length(snd(t))`。五种动作都不能减小这个量：写入保留已有单元，移动把单元从一个列表转移到另一个列表，越过已表示的边界只会补一个空白。因此旧条件蕴含 `n <= m`。特别地，任何机器都不能在这个旧接口下把 `1` 输出为 `0`。

**影响：** 旧的具体机器归约闭包定理仍是其狭窄定义下的有效条件定理；但“所有原始递归函数都有该接口下的机器实现”不可能成立。不能把这个前提仅当作尚未花时间补的普通证明。此结论不单独否定 `pr_self_hardwire_code` 的特定实现可能性，也不推翻不依赖该接口的自停机不可判定证明。

**本次修复：**

- `Turing_Tape.thy` 用每个自然位置的符号相等定义半纸带等价；列表之外的符号是空白。纸带等价还要求两端均为合法纸带；配置等价要求控制状态相同。
- 证明扫描、每种动作、一步和任意有限步都尊重该等价。它不会忽略内部空白、移动非零符号，或改变相对读写头位置。
- `computes_number` 改为最终配置与标准一元输出配置内容等价。仍要求最终状态、完整一元输出和头的位置；没有把“停在任意垃圾纸带上”算成正确输出。
- 重新证明输出唯一性、数值计算顺序组合、顺序组合的双向判定输出对应和机器多一归约的判定闭包。
- `literal_numeral_output_not_smaller` 留存旧接口障碍的形式证明。
- `Turing_Basic.thy` 构造恒等、后继、归零机器，并证明归零机器对所有自然输入计算零。这个结论直接验证擦除障碍已解除。另证明归零后再运行后继，对所有自然输入均输出 1，覆盖实际空白填充纸带的交接。

空白等价是表示层的观察关系，不是一条免费清理纸带的机器指令；交接时机器拿到实际留下的纸带。运行保持等价定理确保后续机器无法区分多余的末端空白。

## 4. “标准图灵机”在本项目中的含义

保留单带、双向无限、二元字母表、确定性有限控制；初态为 1，终态为 0。有限列表只记录纸带的有限非默认部分及可能的空白填充。缺省指令作为 `nop` 后停机，终态吸收后续迭代。

当前采用写 0、写 1、左移、右移、空操作的五动作正规形。其操作设计来自 AFP 的 [Universal Turing Machine](https://isa-afp.org/entries/Universal_Turing_Machine.html)，该参考是在 Isabelle/HOL 中建立的。本仓库的证明在 Isabelle/ZF 中重做，不能把参考项目已有的通用性当成本仓库已继承的结果。

README 中的 Wetzel 类比也需要准确：[Paulson 的论文](https://arxiv.org/abs/2205.03159) 使用 Isabelle/HOL 中的 ZFC 库，不是 Isabelle/ZF。它支持跨领域数学整合的动机，不能直接提供这里的 ZF 证明依赖。本次已修正说明。

这个模型不因缺少通用机就不再是图灵机；但目标若包括可靠的通用计算基础，仍需证明足够一般的函数实现或通用模拟。若最终论文采用每次“写入并移动”的七元组记法，则应给出与这里五动作正规形的明确模拟对应，而不能仅声称定义相似。

不建议现在重写所有编码或另建一套相互独立的机器语义。下一步应在已修复的同一模型上建立可组合的有限程序。

## 5. 全部模块的审查结论

| 模块 | 已有/本次结果 | 尚缺什么 |
| --- | --- | --- |
| [Turing_Machine](../Turing_Machines_ZF/Turing_Machine.thy) | 合法纸带与指令、一步/有限运行、停机与有限运行等价 | 与其他教材表示的显式模拟尚未提供 |
| [Turing_Tape](../Turing_Machines_ZF/Turing_Tape.thy)（新增） | 忽略末端空白的配置等价、任意步保持、列表跨度不减 | 如需商集形式的数学纸带，可由此继续；当前接口无需先构造商集 |
| [Turing_Coding](../Turing_Machines_ZF/Turing_Coding.thy) | 自然数配对、列表编码、机器编号、全自然数解码 | 数字编号本身不提供通用机器 |
| [Turing_Primrec](../Turing_Machines_ZF/Turing_Primrec.thy) | 对象层 `prim_rec` 的算术、配对和列表证书 | 这些是集合函数证书，尚不是有限机器程序 |
| [Turing_Evaluator](../Turing_Machines_ZF/Turing_Evaluator.thy) | 数值一步和有限步与集合机器精确交换 | 实际执行求值器的有限机器 |
| [Turing_Evaluator_Primrec](../Turing_Machines_ZF/Turing_Evaluator_Primrec.thy) | 有界停机谓词的原始递归证书 | 内部一阶公式及满足关系对应 |
| [Turing_Decidability](../Turing_Machines_ZF/Turing_Decidability.thy) | 判定语义、对角语言；自停机的抽象变换接口 | 半判定/可枚举集合的完整统一接口 |
| [Turing_Transformations](../Turing_Machines_ZF/Turing_Transformations.thy) | 具体拒绝变换解释该接口，无条件自停机不可判定；有限输入硬接线 | 通用函数实现 |
| [Turing_Transformations_Primrec](../Turing_Machines_ZF/Turing_Transformations_Primrec.thy) | 数字硬接线与语义构造相等，原始递归多一归约 | 这张数字映射的机器实现 |
| [Turing_Composition](../Turing_Machines_ZF/Turing_Composition.thy) | 同时处理显式与缺省停机的双向顺序交接 | 更一般的循环、分支和参数保存基础 |
| [Turing_Reduction](../Turing_Machines_ZF/Turing_Reduction.thy)（修复） | 内容等价下的数值输出、唯一性、归约闭包 | 由足够一般的程序编译器提供实现见证 |
| [Turing_Basic](../Turing_Machines_ZF/Turing_Basic.thy)（新增） | 恒等、后继、归零的具体有限机器 | 后续基础程序已见下列新增模块；一般组合与原始递归闭包仍缺 |
| [Turing_Programs](../Turing_Machines_ZF/Turing_Programs.thy) / [Turing_Arguments](../Turing_Machines_ZF/Turing_Arguments.thy) | 有限执行路径、纸带计算与顺序组合、多参数编码及内容等价下的唯一性 | 已满足下一层基础程序所需接口 |
| [Turing_Copy](../Turing_Machines_ZF/Turing_Copy.thy) / [Turing_Arithmetic](../Turing_Machines_ZF/Turing_Arithmetic.thy) | 八状态复制机、九状态加法机；具体机器实现 `pr_double` | 一般参数表复制、一般函数组合 |
| [Turing_Storage](../Turing_Machines_ZF/Turing_Storage.thy) / [Turing_Projection](../Turing_Machines_ZF/Turing_Projection.thy) | 擦除参数表、删除首参数、任意下标投影、库中完整 `SC` 的机器实现 | 保存参数时执行子程序的保护定理 |
| [Turing_Realisation](../Turing_Machines_ZF/Turing_Realisation.thy) / [Turing_Context](../Turing_Machines_ZF/Turing_Context.thy) | 所有常数函数、多参数到一元接口桥梁；无自动工作区保护的反例 | `COMP`、`PREC` 的编译构造与正确性 |
| [Turing_Primrec_Reduction](../Turing_Machines_ZF/Turing_Primrec_Reduction.thy) | 自停机到空输入停机的 PR 归约；保留实际机器实现前提 | 消去该前提，得到无条件空输入停机不可判定 |
| [Turing_CH](../Turing_CH/Turing_CH.thy)（扩充） | CH 非不变性；统一真值经析取转成不变性；停机与非停机两侧条件结论 | 具体内化、有效公式编码、算术真理层 |

没有找到原有 theory 中的 `sorry`、额外 `axiomatization` 或 oracle。存在两个有意公开的 locale：拒绝变换接口已由具体机器解释；`halting_sentence` 尚未由具体公式解释。二者不能一概写成“假设已经消去”。

## 6. EPQ 的理论与内容

### 有效的中心论证

EPQ 第 V 节的中心是：算术真理在传递模型之间固定，而一个固定句子 `sigma` 已在模型之间有分歧。于是

```text
F(code(theta)) = code(theta^omega OR sigma)
true_arithmetic <=_m invariant_sentence_codes
```

若算术句子为真，析取在每个模型中都真；若为假，析取继承 `sigma` 的分歧。非法算术代码映射到 `sigma`，正确处理了全自然数归约的补充分支。结合算术真理不可算术定义，得到不变句子代码集不是算术集合。

这个论证的假设与方向是一致的。CH 的作用只在提供一个非不变句子；它不决定某台机器是否停机，也不需要为每个机器代码重新做 forcing。

### 必须保持的限定

1. **模型存在假设。** 对所有传递 ZFC 集模型取不变性时，需明示存在可数传递 ZFC 模型，以调用 CH 分歧构造；这比 `Con(ZFC)` 强。若模型类为空，不变性对所有闭句真空成立。[AFP Independence_CH](https://isa-afp.org/entries/Independence_CH.html) 明确采用这个前提，当前代码也保留了它。
2. **哲学判准不是额外数学定理。** “新增公理只能选择而不能真正解决 CH”依赖 EPQ 选定的原模型类及 `genuinely resolves` 定义。定理不排除一个独立辩护的更小模型类或唯一意向宇宙；EPQ 当前正文已经保留这一限定。标题与口头介绍也应保留。
3. **非算术强于两侧不可枚举。** 停机及其补集的两条归约可以排除可枚举与余可枚举，但不能独自推出非算术；后者仍需全部算术真理的有效翻译及其不可定义性。
4. **绝对性不等于语法已构造。** 传递模型共享标准自然数，为有限计算提供绝对性依据；`prim_rec` 成员资格本身并不生成 Isabelle 的 `formula` 对象，也不自动生成 `sats` 证明。

EPQ 当前摘要和结论总体已正确区分模型不变性与形而上确定性。建议后续保持这个数学陈述，不把“no algorithm recognises discovery”脱离论文指定的判准单独当作普遍哲学结论。

## 7. 与 EPQ 结尾逐级接通

### 第一级：可计算性基础和停机结论

多参数约定、具体基础程序及全部 PR 初始函数现已实现。接下来证明一般组合和原始递归的机器实现闭包，再得到所需 PR 函数的本模型机器见证。由此兑现 `pr_self_hardwire_code` 的机器实现前提，并证明无条件的空输入停机不可判定。进一步构建数值求值器的实际机器实现及通用模拟。

验收必须给出具体有限机器或编译构造、其合法性及双向模拟/输出定理。只追加一个带“存在实现”假设的 locale，不算完成。

### 第二级：机器执行到模型内部句子

构造闭合的 `halt_fm(e)`，证明对每个自然数 e、每个传递 ZFC 模型 M：

```text
(M, [] satisfies halt_fm(e)) <-> halts_blank(decode_machine(e))
```

同时建立代码到公式的有效构造，而非任意集合论选择函数。内部模型必须包含相应自然数、解码机器和有限运行见证。最终具体解释 `halting_sentence`。

技术路径可以复用数值求值器的 PR 证书，但应先用一个基础函数及一次递归的公式表示和 `sats` 证明验证方法，再扩展到整个求值器。原设计笔记把数值路线称为“更短”只是路线判断，目前没有完成的公式实现或工作量证据支持它。直接有限运行路线仍是替代方案。

### 第三级：EPQ 停机版本

对固定非不变闭句 `sigma`，构造自然数代码函数：

```text
f(e) = code(halt_fm(e) OR sigma)
g(e) = code(NOT halt_fm(e) OR sigma)
```

证明它们可计算，并建立停机集和其补集各自到不变句子代码集的归约。加入半判定/可枚举集合定义和必要闭包定理，才能正式得出既非可枚举也非余可枚举。

本次新增的 `nonhalting_or_invariant_iff_not_halts_blank` 补上了第二条的条件语义部分；它不等于已经完成有效归约。

### 第四级：EPQ 的完整终点

构建算术句法、标准算术满足关系、到集合论句法的有效翻译，证明所有闭算术句在传递 ZFC 模型中的满足关系与标准算术一致。定义不变闭句的自然数代码集合并处理非法代码。

然后实例化本次抽出的 `uniform_or_invariant_iff`，证明 `Th(N) <=_m I_TrZFC`，再以算术不可定义性和可计算原像闭包推出非算术性。这一层原先没有进入 README 的完整路线，不能用停机层完成来代替。

可以先将全体传递 ZFC 模型作为第一正式目标；EPQ 对任意有分歧模型类 K 的推广随后以显式模型类参数处理。不要把对某个集合编码的模型族的定理默认为对所有传递集模型的定理。

## 8. 本次验证

验证环境：Isabelle2025-2，AFP 2026-02-06。2026-09-07 最终运行：

```sh
/Applications/Isabelle2025-2.app/bin/isabelle build -v -D .
```

结果：退出码 **0**。`Turing_Machines_ZF` 与 `Turing_CH` 均从修改后的源文件完成构建；总耗时 **2 分 44 秒**，其中 CH 会话约 **2 分 21 秒**，包含其 AFP 导入理论的检查。这里没有将启动时命中缓存的基线检查冒充修改后的证明验证。

本次内核接受的关键结果包括 `steps_config_eq`、`steps_span_mono`、`literal_numeral_output_not_smaller`、`computes_number_unique`、`computes_number_sequential`、`computes_number_then_yields_iff`、原有归约闭包和 PR 条件定理、`identity_computes`、`successor_computes`、`zero_computes`、`zero_realises_constant`、`zero_then_successor_computes_one`、`uniform_or_invariant_iff` 及非停机析取条件定理。

当前两个源目录的证明绕过扫描无匹配，临时诊断代码已移除，`git diff --check` 通过。`AI_USAGE.md` 和 `papers/EPQ.pdf` 无差异。改动在本地工作区，未推送到 GitHub。

复现边界：此轮使用机器上已有的 Isabelle/AFP 安装，没有重新下载依赖；AFP 目录由 `.gitignore` 排除，不随仓库分发。尚无仓库 CI 配置。构建证明当前源文件在该版本环境中通过，不应描述为另一个全新环境的独立复现。

## 9. 2026-09-08：从基础机器推进到原始递归的初始函数

本轮已落实用户授权的接管推进，新增八个 theory。所有程序继续使用同一单带、双向无限、二符号、有限控制模型。

- **多参数表示。** 每个 `n` 编成 `n+1` 个 1，随后一个 0。证明 `arguments_eq_imp_equal`，即在忽略末端空白后仍可恢复唯一的自然数参数表。空参数表与参数值零没有混淆。
- **真实复制与加法。** 八状态 `copy_machine` 逐个擦除、复制、恢复源记号，证明任意块长下的终止和输出。九状态 `addition_machine` 连接两个正长度块、删除三个编码用记号，证明输出普通一元的 `n+m`。机器组合得到 `doubling_realises_pr_double`；包括 `n=0` 的整个自然数域都在定理范围内。
- **清理和投影。** 实现删除首参数、擦除任意参数表、保留首块并擦除其余参数、回到输出起点。由此构造任意自然下标 `projection_machine(i)`，包含参数不足时输出零的行为。
- **完整初始函数。** `tm_realises_arguments` 量化所有自然数列表。`keep_first_realises_SC`、`projection_realises_PROJ`、`constant_arguments_realises_CONSTANT` 分别给出库中后继、全部投影、全部常数的有限机器见证。库中 `SC` 对空列表输出零，这一点保留在实现中。
- **接口衔接。** `argument_realiser_to_unary` 通过具体后继机器把旧的一元输入接入新参数表示；输出和顺序交接使用真实的空白填充纸带。
- **防止错误推广。** `numerical_realisation_does_not_imply_frame` 给出一个三状态反例：它在原数值契约下实现恒等，却会擦除头左边保存的一个 1。因此不能从独立运行正确推断在保留参数的环境中运行正确。

本轮没有增加实现假设或用条件 locale 代替程序。原始递归初始函数已实现，**一般 `COMP` 和 `PREC` 闭包仍未证明**。通用机、`pr_self_hardwire_code` 的机器见证、内部停机公式和 EPQ 非算术性也仍未完成。

2026-09-08 最终运行同一环境中的：

```sh
/Applications/Isabelle2025-2.app/bin/isabelle build -v -D .
```

退出码 **0**，`Turing_Machines_ZF` 与 `Turing_CH` 均成功，总耗时 **3 分 15 秒**；其中 CH 会话约 **2 分 56 秒**。新增八个 theory 的全部证明在此构建中接受检查，包括上述工作区反例。两个源码目录的证明绕过扫描无匹配，新文件空白格式检查与 `git diff --check` 通过。`AI_USAGE.md` 和 EPQ 原稿未改动。

成果保存在本地开发分支 `codex/turing-program-foundations`，未推送到 GitHub。复现环境的边界与第 8 节相同。

## 10. 下一项最重要的工作

下一项是**保存原参数和中间结果时的子程序执行语义**。它是一般 `COMP` 和 `PREC` 实现的共同前提：组合要在同一输入上求多个函数，递归要同时保存原参数、计数器和累计结果。

目前倾向于建立受明确工作区边界约束的编译程序及其保存定理，继续编译到现有二符号单带模型。若使用额外轨道或寄存器作为中间表示，必须同时给出回到现有模型的具体模拟，不能把中间模型的指令当作免费操作。当前反例排除了仅凭 `tm_realises_unary` 就把任意现成程序放到保存区旁边的做法；它不否定通过真正的编译变换获得一般实现定理的可能性。

这一层完成后，依次证明 `COMP`、`PREC` 闭包，消去自硬接线归约的机器实现前提，再落实通用求值器和 Module III。EPQ 的最终验收仍是第 7 节第四级的 `Th(N) <=_m I_TrZFC` 及非算术性，不能被基础函数或停机层的完成替代。

## 11. 2026-10-04：工作区保存、模型见证与公开复现

### 11.1 有界执行的保存定理

新增 `Turing_Workspace.thy`。`frame_config` 在工作区两侧附加保存的数据；这只是原二符号纸带上的布局，没有引入新的机器指令。

`steps_preserve_frame` 证明：若工作区左右各有至少 `n` 个单元，则执行 `n` 步与在执行结果外重新附加同一保存区严格相等。`bounded_workspace_history` 进一步对任意配置各补 `n` 个空白，证明每一个 `k <= n` 的运行前缀都保持保存区，并与原配置运行的纸带内容等价。结论包含头位置，不只是结果数值。

这个定理解决了显式时间上界下的隔离。它没有给任意停机程序计算时间上界，也没有把一般 `COMP`、`PREC` 实现问题化为已解决。下一项仍是可实际执行的存储管理与子程序编译：必须证明程序自身能够维护边界，不能把预先知道整个运行长度当作免费操作。九月的反例依然有效。

### 11.2 传递模型中的有限运行证书

新增 `Turing_Models` 会话及 `Turing_Model_Witnesses.thy`。先在 AFP 已有的 `M_trivial` 中证明有限列表和有限函数的封闭性，再从项目实际使用的 `transitive_zfc_model` 定义导出该 locale，而不是另加一个未经兑现的模型接口。

由此证明每个传递 ZFC 集模型都包含任意有限机器、配置以及规范运行轨迹 `lambda k in succ(n). steps(P,c,k)`，也包含每个自然数机器代码解码得到的机器。

`transitive_zfc_halting_witness_iff` 证明外部停机当且仅当模型内存在相应有限证书；还给出任意两个传递模型在此证书存在性上的一致性，以及空输入、自然代码版本。

边界必须保留：证书条件中的 `finite_run` 仍是外部集合论谓词。此处没有构造 `finite_run_fm` 或 `halt_fm(e)`，没有证明它们的 `sats` 充分必要条件，也没有消去 `halting_sentence` 的公式前提。完成的是直接有限运行路线的见证成员性义务。

### 11.3 仓库呈现与复现

README 改为研究入口，集中展示定义、已有成果、语义修正和剩余证明；详细定理说明移到 `documentation/DEVELOPMENT.md`。三个旧 RV 和原 AI 协助声明保留在 `documentation/history/`，避免旧状态与当前结果混读。新版协助声明明确区分研究问题、原始工作、后续 AI 实现和实际复核范围；没有将代码整理改写为独立作者或专家评审声明。EPQ 原稿未改动。

增加固定 Isabelle2025-2 / AFP 2026-02-06 依赖、校验和、三个会话的 GitHub Actions 构建、公开构建日志、相对链接检查和引用元数据。复现步骤集中在 `documentation/BUILD.md`。这次发布还包含此前只保存在本地的九月纸带语义修正与具体程序基础。

### 11.4 本地验证

2026-10-04 对最终源文件运行 `isabelle build -c -v -D .`，三个会话全部成功，退出码 **0**，总耗时 **54 秒**。这是清除目标会话后的重建，包含 AFP 导入理论的检查；仍使用本机已有的固定版本依赖。无证明绕过标记，公开 Markdown 相对链接检查通过；还以临时坏链接和证明绕过标记验证了检查脚本确实会拒绝这些情况，随后移除了探针文件。
