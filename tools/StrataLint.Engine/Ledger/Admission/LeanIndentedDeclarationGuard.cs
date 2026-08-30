using System.Collections.Immutable;

namespace StrataLint.Engine;

// 缩进声明守卫:Lean 命令必须起于第 0 列,故任何【缩进行的首个 token】若看起来像
// 声明,就说明提取器读到了它无法忠实还原的形状,一律 fail-closed 拒绝 —— 它挡的是
// 「顶层陈述看着没变,却在缩进处偷加/偷改定义」这一类语义削弱。
internal sealed partial class LeanSourceCatalog
{
    // Lean 标识符可含字母、数字、`_`、`'`、`?`、`!`、`.`(限定名)与 Unicode 字母;
    // 运算符与标点(`-`、`(`、`:`、`,` …)一律不是。判首字符即可区分本例。
    private static bool IsIdentifierToken(string text) =>
        text.Length > 0 && (char.IsLetter(text[0]) || text[0] == '_');

    private static void RejectIndentedDeclarations(
        ImmutableArray<LeanSourceToken> tokens,
        ImmutableArray<int> commandStarts,
        RepoPath path)
    {
        var recognized = commandStarts.ToImmutableHashSet();
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token.Column == 0
                || recognized.Contains(index)
                || index > 0 && tokens[index - 1].Line == token.Line)
            {
                continue;
            }

            if (token.Text == "@"
                && tokens[index..Math.Min(tokens.Length, index + 32)].Any(candidate =>
                    candidate.Line == token.Line && DeclarationKinds.Contains(candidate.Text))
                || DeclarationKinds.Contains(token.Text) && token.Text != "constant"
                // `constant` 在 Lean 4 已不是声明关键字(被 `opaque` 取代)。实测
                // 4.31 与 4.33:`constant foo : Nat := 1` 均报
                // `unexpected identifier; expected command`,而
                // `def bar (constant : Nat) := constant - 0` 被接受。
                // 故仅当其后【紧跟标识符】时才可能是 Lean 3 遗留的声明形;
                // 紧跟运算符者是项,不是声明。本仓
                // D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.lean:98
                //     constant - (Fintype.card State : Real) * coefficient state action
                // 即此形:行内的 `:` 来自类型标注,旧判据据此误判为缩进声明,
                // 使整条 mathlib 升级授权路径恒 false。
                || token.Text == "constant"
                    && index + 1 < tokens.Length
                    && tokens[index + 1].Line == token.Line
                    && IsIdentifierToken(tokens[index + 1].Text)
                    && tokens[index..Math.Min(tokens.Length, index + 32)].Any(candidate =>
                        candidate.Line == token.Line && candidate.Text == ":")
                || token.Text is "private" or "protected" or "noncomputable" or "partial" or "unsafe"
                    && tokens[index..Math.Min(tokens.Length, index + 32)].Any(candidate =>
                        candidate.Line == token.Line && DeclarationKinds.Contains(candidate.Text)))
            {
                throw new LeanSourceExtractionException(
                    $"Indented Lean declaration is unsupported in {path.Value}.");
            }
        }
    }
}
