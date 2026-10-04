# Isabelle/ZF 集合编码计算：全程技术审查

审查基线：Git 提交 `3a454f76d417e2cd133c5398aabb2c1d29269315`，2026-10-04。本文是供下一步架构判断使用的证据清单，不作 AFP 投稿范围的决定，也不把未完成的 EPQ 终点写成既成定理。

后续依赖整理将核心理论移入 `Turing_Machines_ZF/Core`，并把拒绝变换拆为 `Turing_Rejection.thy`。下文的历史过程仍以所列基线为准；文件链接指向整理后的实际位置。

## 1. 审查方法与证据等级

本报告按三个 Isabelle 会话、其 `ROOT`、源码中的定义和定理、Git 提交史、现有技术记录及公开 CI 记录核对。"已证明"指 Isabelle 在给定定义与前提下接受了定理；"语义审查"指另行检查这些定义是否表达目标。构建通过不替代后一种判断。本文没有逐行独立重证约二十余个长 theory，也不是外部专家评审。EPQ 原稿保留为研究来源；本报告只审核仓库中与其结论相接的形式化路径。

当前公开 Linux 构建对应同一基线提交，运行记录为 [GitHub Actions 37200695987](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/runs/37200695987)，三个项目会话的检查通过。构建环境固定 Isabelle2025-2 与 AFP 2026-02-06；见 [`documentation/BUILD.md`](../documentation/BUILD.md)。这证明该版本在固定环境中可重建，不证明定义恰当、新颖性或 AFP 接收价值。

## 2. 研究问题与现有边界

原始目标来自 [`EPQ.pdf`](EPQ.pdf) 第 V 节：以真算术 `Th(N)` 为源，构造到传递 ZFC 集模型间不变闭句代码集合的有效多一归约，从而在可数传递 ZFC 模型存在等前提下，推出该代码集合非算术。CH 在论证中提供一个固定的非不变闭句；它不编码某台机器的停机事实。

仓库目前实际包含三层：`Turing_Machines_ZF` 中的集合编码图灵机与可计算性结果；`Turing_CH` 中的模型不变性及条件性析取原则；`Turing_Models` 中的有限运行见证和部分算术公式满足关系。第一层可单独构建；后两层依赖 AFP 的 `Independence_CH` 及其基础。

```text
Isabelle/ZF
  -> Turing_Machines_ZF             机器、编号、运行、变换、程序
  -> Turing_CH                      CH 分歧与条件性不变性接口
  -> Turing_Models                  有限见证、部分算术真理语义

完整 EPQ 终点需要：一般算术句法 -> 有效公式翻译
  -> 任意闭句的满足关系正确性 -> 有效自然数代码映射
  -> 真算术到不变句代码的多一归约 -> 非算术性。
```

这条最终链尚未闭合。停机公式路线与直接算术翻译路线可以共享模型和编码基础，但前者不是后者的必要前提。

## 3. Git 历程：具体增加和改正了什么

| 时段与提交 | 可以从仓库核对的工作 | 不能由提交名推断的事 |
| --- | --- | --- |
| 4—7 月：`b21582d`、`54b1b3e`、`70191c4` | 初版仓库、v0.1 和项目命名 | 初版输出契约后来发现有问题；不能把 v0.1 当成当前证明范围 |
| 8 月初：`b9c2c17`、`0bf44ce`、`21a7419` | 指令流和机器的自然数编号、数值求值、对角语言与自输入停机不可判定的基础 | 数值求值器是集合层函数，不是已编出的通用图灵机 |
| 8 月：`7b14efc`、`09ff20f`、`6fb8e25` | 语义输入硬接线、其原始递归代码函数、机器多一归约接口 | 原始递归代码函数尚未有本模型中的机器实现见证 |
| 9 月：`451d85c` | 修正输出语义；实现基础程序、多参数表示、复制、加法、常数、后继、投影；给出工作区反例 | 一般 `COMP`、`PREC` 机器闭包仍未证明 |
| 10 月：`ead82b5` | 有界工作区保护；传递模型内有限运行证书 | 外部证书谓词尚未变成内部一阶公式 |
| 10 月：`74f4e32`、`a62c11d`、`74b6f59` | README、构建说明、披露、固定依赖和 CI；清洁构建修正；EPQ 假设表述修正 | 文档和 CI 不等于独立同行评审 |
| 10 月：`4fdee34`、`3a454f7` | 受自然数限制的量词、零/后继/序及加乘公式的模型满足关系 | 尚无完整算术句法归纳、有效翻译或最终归约 |

这张表描述 Git 中的工作增量，不据此分配每一行证明的个人手写贡献。项目的实质性 AI 协助已单独披露于 [`AI_USAGE.md`](../AI_USAGE.md)；该文件也明确指出构建成功不等于作者逐行人工审阅。

## 4. 基础机器：表示、一步语义和有限运行

[`Turing_Machine.thy`](../Turing_Machines_ZF/Core/Turing_Machine.thy) 把字母表定义成二元集合，动作编码为写 0、写 1、左移、右移、空操作五个值。机器是有限指令列表，每个指令携带动作和下一状态；配置为自然数状态与纸带的有序对。纸带用两个有限符号列表表示，以读写头为分界；未显式表示的位置按空白解释。左侧列表按离头部最近的单元在前排列，右侧列表首元素是当前扫描单元。

`slot(q,b)` 将非终态和读到的符号映射到指令表位置。`fetch` 对终态或越界指令位置返回 `nop` 后进入终态，因此有限表和缺省行为均有定义。`update` 实现五种局部纸带动作；`step` 执行一次，`steps` 执行自然数次。终态吸收后续运行。文件证明类型保持、扫描/更新规律、有限步与运行轨迹的基本性质，并将外部停机与有限运行证书联系起来。这里的"标准图灵机"是单带、双向无限、二元字母、确定性有限控制的五动作正规形；若要与另一种写后即移的指令格式比较，尚需显式模拟定理。

## 5. 首次语义审查发现的问题：有限列表不是整条纸带

早期 [`Turing_Reduction.thy`](../Turing_Machines_ZF/Turing_Reduction.thy) 的数值输出要求最终列表与规范一元输出列表**字面相等**。但五种动作不会减少两个列表总长度：写入保留已表示单元，移动转移单元，越过边界还可能添入空白。因此旧接口使输入 `n` 输出比 `n` 短的程序不可能满足定义，归零就是反例。这不是少写一个证明，而是定义错配。

[`Turing_Tape.thy`](../Turing_Machines_ZF/Core/Turing_Tape.thy) 以所有位置上的内容相等定义 `half_tape_eq`，再定义纸带和配置等价；有限列表末端的多余空白被忽略，读写头位置与内部非空白内容仍保留。`steps_config_eq` 证明等价配置经任意有限步仍等价。数值计算的输出契约随之改为配置内容等价，同时仍要求终态和规范头部布局。旧接口导致的跨度障碍保留为形式定理，归零与后继的具体程序则检验新契约允许真正擦除。

这一修复还进入组合、输出唯一性和归约的下游证明，不能只在 README 中改一句解释。它展示了本项目最重要的审查原则：内核可证明旧定义下的命题，但不能保证旧定义表达原来的计算意图。

## 6. 编号、数值求值、对角化与归约

[`Turing_Coding.thy`](../Turing_Machines_ZF/Core/Turing_Coding.thy) 逐层构造自然数配对、自然数列表、指令及机器代码；证明编码/解码互逆所需的类型与等式。`decode_machine` 对所有自然数代码给出合法机器，避免对角化时遇到非法代码的空洞。该编号是集合函数层的数学编号，不是通用机器。

[`Turing_Evaluator.thy`](../Turing_Machines_ZF/Core/Turing_Evaluator.thy) 为纸带和配置赋数值代码，定义代码层的扫描、更新、取指、一步与有限步函数。`code_step_correct`、`code_steps_correct` 将数值运算与原机器运行交换；末段把代码层有界停机测试与外部停机事实接通。[`Turing_Primrec.thy`](../Turing_Machines_ZF/Turing_Primrec.thy) 与 [`Turing_Evaluator_Primrec.thy`](../Turing_Machines_ZF/Turing_Evaluator_Primrec.thy) 为配对、列表及代码层有限求值建立 Isabelle/ZF 对象层 `prim_rec` 证书。这些证书仍不能自动产生执行该函数的有限指令表，更不能自动产生 ZF 内部的 `formula`。

[`Turing_Decidability.thy`](../Turing_Machines_ZF/Core/Turing_Decidability.thy) 明确定义机器的接受、拒绝与判定，以及对角拒绝语言、自输入停机集合、空输入停机集合。对角拒绝不可判定先由编号和自指矛盾得到。随后现已拆出的 [`Turing_Rejection.thy`](../Turing_Machines_ZF/Core/Turing_Rejection.thy) 构造具体的拒绝变换：改写原机器到终态的行为并附加检查控制，证明它在输入上的停机恰对应原机拒绝，从而消去 `halting_diagonal` 的抽象变换前提，得到**无条件的本模型自输入停机不可判定**。

同一变换理论构造有限输入硬接线：加载指定一元输入后转入移位后的原机。[`Turing_Transformations_Primrec.thy`](../Turing_Machines_ZF/Turing_Transformations_Primrec.thy) 在数字代码上逐项实现移位和加载，证明数字变换与语义构造一致，且自硬接线函数属于 `prim_rec`。[`Turing_Primrec_Reduction.thy`](../Turing_Machines_ZF/Turing_Primrec_Reduction.thy) 因而得到自输入停机到空输入停机的**原始递归多一归约**。但其空输入停机不可判定定理 `self_hardwire_realiser_imp_blank_halting_undecidable` 明写前提：存在实现该硬接线函数的图灵机。此机器见证尚未构造，故不能省略条件。

[`Turing_Composition.thy`](../Turing_Machines_ZF/Turing_Composition.thy) 对两台机器作控制状态移位和顺序拼接，证明首阶段、次阶段的模拟及终止对应；[`Turing_Reduction.thy`](../Turing_Machines_ZF/Turing_Reduction.thy) 用修正后的输出契约建立数值计算的顺序组合和机器多一归约的判定性闭包。这里的顺序交接是已有定理；它不是任意原始递归函数 `COMP`/`PREC` 的编译定理，因为后者还需要保存参数、中间结果和工作区。

## 7. 具体有限程序：小成果及各自作用

| 位置 | 具体实现与证明 | 能说明什么 |
| --- | --- | --- |
| [`Turing_Basic.thy`](../Turing_Machines_ZF/Turing_Basic.thy) | 恒等、后继、归零指令表；归零接后继 | 检验输出等价允许擦除，且真实纸带可交给下一台机 |
| [`Turing_Arguments.thy`](../Turing_Machines_ZF/Turing_Arguments.thy) | 每个参数 `n` 用 `n+1` 个 1 后接空白分隔；`arguments_eq_imp_equal` | 即使忽略末端空白，参数列表仍可恢复；零与缺失不混同 |
| [`Turing_Copy.thy`](../Turing_Machines_ZF/Turing_Copy.thy) | 八状态复制机；逐个标记、复制、恢复；`copy_block_computes` | 给出真实的任意长度复制，不把复制作免费原语 |
| [`Turing_Arithmetic.thy`](../Turing_Machines_ZF/Turing_Arithmetic.thy) | 九状态加法机；处理两个编码块与分隔符；再与复制机组合得到 `doubling_realises_pr_double` | 证明具体加法与一个非平凡 `prim_rec` 函数的机器见证 |
| [`Turing_Storage.thy`](../Turing_Machines_ZF/Turing_Storage.thy) / [`Turing_Projection.thy`](../Turing_Machines_ZF/Turing_Projection.thy) | 擦除参数、删首参数、保留首参数、任意下标投影；处理空表和短表 | 支撑完整 `SC` 与 `PROJ` 初始函数，不只展示单个样例 |
| [`Turing_Realisation.thy`](../Turing_Machines_ZF/Turing_Realisation.thy) | 构造任意常数程序、参数版后继，并衔接一元输入接口 | 给出 `CONSTANT`、`SC`、`PROJ` 的具体机器基础；未给出一般闭包 |

[`Turing_Programs.thy`](../Turing_Machines_ZF/Turing_Programs.thy) 提供有限到达路径和纸带计算的共同接口，使上述具体运行证明可以组合。所有程序仍在同一二符号单带模型中，不借用未定义的寄存器、轨道或外部子程序操作。

## 8. 工作区问题：反例、正面定理和未解决的跳跃

[`Turing_Context.thy`](../Turing_Machines_ZF/Turing_Context.thy) 的 `scratch_identity_machine` 在空白背景下实现恒等，却会擦除头左侧预存的一个 1。`numerical_realisation_does_not_imply_frame` 因而形式化证明："单独算对函数"不能推出"嵌入保存数据的纸带时安全"。一般 `COMP` 和 `PREC` 不能直接把现有程序当无副作用函数调用。

[`Turing_Workspace.thy`](../Turing_Machines_ZF/Core/Turing_Workspace.thy) 对保存数据 `L,R` 定义 `frame_config(c,L,R)`，把它们接在有限工作区两侧。`steps_preserve_frame` 以归纳证明：若两个半纸带初始至少各有 `n` 个工作单元，则执行 `n` 步后，带保存数据的运行与先运行再加保存数据**配置字面相等**。`bounded_workspace_simulation` 和 `bounded_workspace_history` 先在两侧填入 `n` 个空白，得到所有 `k <= n` 前缀的保护与原运行的内容等价。

该定理给定**外部提供的时间界**时非常强；它没有给任意程序预测停机时间的可计算上界，也没有证明一个机器程序能自动维护所需缓冲区。反例与正面定理同时存在，精确标出了通用编译尚缺的操作性义务。

## 9. 模型层与 EPQ 接口

[`Turing_CH.thy`](../Turing_CH/Turing_CH.thy) 用 `Transset(M) ∧ M ⊨ ZFC` 定义模型，用所有此类模型对闭句的真值一致定义 `zfc_invariant`。`CH_not_invariant` 在给定可数传递 ZFC 模型时调用 AFP `Independence_CH` 的构造，取得 CH 与非 CH 模型。`uniform_or_invariant_iff` 证明一般原则：如果闭句 `φ` 在每个目标模型中都具有同一个外部真值 `P`，而固定闭句 `σ` 在目标模型间有分歧，则 `Or(φ,σ)` 的不变性恰等价于 `P`。

`halting_sentence` locale 将 `halt_fm(e)` 的闭合、类型及 `sats_halt_fm_iff` 当作**假设**，在这些前提下得到停机/非停机与不变性的条件性等价。文件中 `halting_or_CH_invariant_iff_halts_blank` 仍在该 locale 内。尚无具体 `halt_fm` 实例解释 locale；不能把该等价写成已完成的有效停机归约。

[`Turing_Model_Witnesses.thy`](../Turing_Models/Turing_Model_Witnesses.thy) 从仓库的传递 ZFC 模型条件进入 AFP 的模型 locale，证明合法机器、配置及规范有限轨迹均属于每个模型。`transitive_zfc_halting_witness_iff` 将外部停机与模型中存在有限证书等价，并推出不同传递模型对这种证书存在性一致。证书中的 `finite_run` 仍是外部谓词："见证集合在模型里"不等于"内部一阶公式对它的解释正确"。

[`Turing_Arithmetic_Truth.thy`](../Turing_Models/Turing_Arithmetic_Truth.thy) 走另一条直接路径：显式自然数域公式、零、后继、`<`、加法、乘法及受 `nat` 限制的存在/全称量词有对应 `sats` 等价定理。加乘定理调用 AFP 的基数算术公式，并在自然数参数上证明它们确实表达普通 `#+`、`#*`。这些是**原子关系与量词接口**；还没有递归的源算术句法、任意公式的翻译函数、闭句真值归纳、自然数代码的有效性或 Tarski 侧非定义性在此目标中的组合。

## 10. 可复核的当前结论与禁止跨越的断言

| 命题 | 当前状态 | 精确阻碍 |
| --- | --- | --- |
| 这是一套 Isabelle/ZF 中的单带二元确定性图灵机语义 | 已实现并构建 | 与其他指令格式的等价尚未证明 |
| 机器可自然数编号，数值有限步求值准确 | 已证明 | 尚无执行该求值器的通用图灵机 |
| 自输入停机不可判定 | 已证明，具体拒绝变换消去抽象前提 | 不应与空输入停机混称 |
| 自输入停机原始递归归约到空输入停机 | 已证明 | 将该函数实现为机器后才得到无条件机器层结论 |
| 常数、后继、投影、复制、加法等具体程序 | 已证明 | 不蕴含任意 `COMP`、`PREC` |
| 给定 `n` 步上界的保存数据保护 | 已证明 | 缺自动产生与维护工作区的编译程序 |
| 传递模型含有限运行证书 | 已证明 | 尚无内部 `finite_run_fm`/`halt_fm` 及其 `sats` 充分必要性 |
| CH 可提供非不变句；统一真值经析取转为不变性判断 | 已证明，CH 侧要求可数传递模型存在 | `halting_sentence` 的具体解释仍缺 |
| 算术零、后继、序、加乘及受限量词在模型中语义正确 | 分项定理已证明 | 尚无全部算术闭句的统一翻译 |
| `Th(N) <=_m I_TrZFC` 与不变代码集非算术 | **未证明** | 有效句法/代码、全公式正确性、归约与不可定义性结尾均待完成 |

通过构建且无 `sorry`、额外公理或自定义 oracle，是证明状态的正面证据；它不消除上述显式 locale 假设，也不把数学上不同的归约强度自动合并。当前代码没有外部专家对新颖性、正确表达或长期维护性的独立评审结论。

## 11. 供下一步架构判断使用的事实边界

`Turing_Machines_ZF` 是仅依赖 Isabelle/ZF 与 `ZF-Induct` 的独立会话，具有从机器语义走到编码、求值、对角化、具体程序和有界工作区的完整可读路径。它内部同时有已闭合的核心结果和面向后续研究的条件接口；选择哪些公开成长期稳定的库接口，需要另作判断。`Turing_CH`/`Turing_Models` 与 EPQ 目标相连，但不能为前一层的独立成果附加一个尚未兑现的"完整 EPQ"标题。

可能的后续方向至少有两种：围绕已闭合的计算基础整理一篇独立条目，或继续推进真算术到模型不变性代码的完整归约。本报告只固定两者的现状和依赖，不替你预先冻结取舍、范围或投稿时机。

## 12. 复核入口

- 从定义入手：[`Turing_Machine.thy`](../Turing_Machines_ZF/Core/Turing_Machine.thy) → [`Turing_Tape.thy`](../Turing_Machines_ZF/Core/Turing_Tape.thy) → [`Turing_Coding.thy`](../Turing_Machines_ZF/Core/Turing_Coding.thy)。
- 从主要计算定理入手：[`Turing_Evaluator.thy`](../Turing_Machines_ZF/Core/Turing_Evaluator.thy) → [`Turing_Decidability.thy`](../Turing_Machines_ZF/Core/Turing_Decidability.thy) → [`Turing_Rejection.thy`](../Turing_Machines_ZF/Core/Turing_Rejection.thy)。
- 从语义反例与修复入手：[`Turing_Reduction.thy`](../Turing_Machines_ZF/Turing_Reduction.thy) → [`Turing_Context.thy`](../Turing_Machines_ZF/Turing_Context.thy) → [`Turing_Workspace.thy`](../Turing_Machines_ZF/Core/Turing_Workspace.thy)。
- 从 EPQ 边界入手：[`Turing_CH.thy`](../Turing_CH/Turing_CH.thy) → [`Turing_Model_Witnesses.thy`](../Turing_Models/Turing_Model_Witnesses.thy) → [`Turing_Arithmetic_Truth.thy`](../Turing_Models/Turing_Arithmetic_Truth.thy)。
- 更细的历史审查与内部公式技术设想见 [`REVIEW_AND_ROADMAP.md`](REVIEW_AND_ROADMAP.md) 和 [`TURING_INTERNALISATION.md`](TURING_INTERNALISATION.md)；历史记录中的旧"待办"须按本报告基线重新解释。
