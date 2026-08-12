using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class LandauerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative information-and-divergence remainder turns an exact heat-entropy balance into a lower bound.",
        H("A Heat-Entropy Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("heat-entropy-balance-implies-the-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/DivergenceSupport/LandauerBound.landauer_bound_of_balance"),
                H("Discarding nonnegative remainders gives the lower bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp,
                    F.Id("beta"), Comma, Sp,
                    F.Id("heat"), Comma, Sp,
                    F.Id("entropyChange"), Comma, Sp,
                    F.Id("mutualInfo"), Comma, Sp,
                    F.Id("divergence"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("beta"), Sp, Cdot, Sp, F.Id("heat"), Sp, Eq, Sp,
                    Minus, F.Id("entropyChange"), Sp, Plus, Sp, F.Id("mutualInfo"), Sp, Plus, Sp,
                    F.Id("divergence"), Sp, Land, Sp,
                    D(0), Sp, Le, Sp, F.Id("mutualInfo"), Sp, Land, Sp,
                    D(0), Sp, Le, Sp, F.Id("divergence"), Sp, Rightarrow, Sp,
                    Minus, F.Id("entropyChange"), Sp, Le, Sp,
                    F.Id("beta"), Cdot, Sp, F.Id("heat")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let beta times the heat be exactly the negative entropy change plus a mutual-information remainder and a divergence remainder. When both remainders are nonnegative, their sum can be discarded, leaving the negative entropy change bounded above by beta times the heat.")),
                    Paragraph(Text(
                        "The balance identity and the two nonnegativity statements are explicit hypotheses. This result does not derive that physical balance law; it isolates the order-theoretic step from the balance to the lower bound."))),
                DescribeRole.Theorem
            )),
        []));
}
