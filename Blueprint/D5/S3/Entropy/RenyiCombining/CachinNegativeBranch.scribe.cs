using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinNegativeBranchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative-parameter certificate makes the binary Renyi elasticity transform decrease.",
        H("Negative-Parameter Elasticity Certificate"),
        Blocks(
            Paragraph(Text("Write n = alpha - 1. This module handles -1 < n < 0, corresponding to "
                + "0 < alpha < 1. It reuses the functions T, A, B and F and the real-power derivative "
                + "identities of CachinElasticityMonotone. All powers use positive bases on (0,1).")),
            Describe.Lean(DescribeId.Create("cachin-negative-antitone-f"),
                DeclarationHandle.Create("D5/S3/Entropy/RenyiCombining/CachinNegativeBranch.antitoneOn_F_neg"),
                H("The elasticity transform is antitone for negative n"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Grp(Seq(F.Id("n"), Colon, Sp, Mathbb, Grp(F.Id("R")))), Comma, Sp,
                    new Formula.Logic(
                        new Formula.Relation(Seq(Minus, D(1)), FormulaRelationOperator.LessThan, F.Id("n")),
                        FormulaLogicOperator.And,
                        new Formula.Relation(F.Id("n"), FormulaRelationOperator.LessThan, D(0))), Sp, Implies, Sp,
                    Call("AntitoneOn", Call("F", F.Id("n")), Call("Ioo", D(0), D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reused four-term function J has J(1)=J'(1)=0 and "
                    + "J''(z)=n(n^2-1)z^(n-2)(1-z). On -1 < n < 0 this is nonnegative. "
                    + "Two applications of derivative monotonicity therefore give J >= 0, and the "
                    + "identity A'(r)=n r^(n-2)J(r^2)/(1-r^(2n))^2 gives A' <= 0. "
                    + "Here A > 0, -1 < B < 0 and B' > 0. Consequently "
                    + "F'=A'/(1+B)-(1+A)B'/(1+B)^2 is strictly negative. "
                    + "The resulting antitonicity is consumed by the convex clause of Hirche's "
                    + "Conjecture IV.18; it does not by itself state convexity in the entropy coordinate."))),
                DescribeRole.Theorem))));
}
