using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class GoldenHeckeMahlerFunctionalEquationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Hecke-Mahler series obeys its exact two-branch monomial substitution law.",
        H("Golden Hecke-Mahler Functional Equation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-hecke-mahler-functional-equation"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/GoldenHeckeMahlerFunctionalEquation.golden_hecke_mahler_functional_equation"),
                H("The coefficient series splits into two substituted branches"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Operatorname, Grp(F.Id("heckeMahlerSeries")), Colon, Sp,
                    Operatorname, Grp(F.Id("Degree")), Sp, To, Sp,
                    Operatorname, Grp(F.Id("Cardinal")), Close,
                    Sp, Eq, Sp, Open,
                    F.Id("d"), Colon, Sp, Operatorname, Grp(F.Id("Degree")),
                    Sp, Mapsto, Sp,
                    Operatorname, Grp(F.Id("pqPBranchSeries")), Open, F.Id("d"), Close,
                    Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("pSquaredQBranchSeries")), Open, F.Id("d"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coefficient at (a,b) counts indices v for which the monomial "
                            + "P^S(v) Q^v has exponent pair (a,b). Under (P,Q) to (PQ,P), "
                            + "the pair becomes (S(v)+v,S(v)); under (P,Q) to (P^2Q,PQ), "
                            + "followed by multiplication by P^2Q, it becomes "
                            + "(2+2S(v)+v,1+S(v)+v). Thus the displayed coefficient equality "
                            + "is exactly the formal-series identity F(P,Q)=F(PQ,P)+P^2Q "
                            + "F(P^2Q,PQ).")),
                    Paragraph(Text(
                        "The proof first derives S(S(v))=S(v)+v from the repository's "
                            + "Zeckendorf digit-shift theorem and Mathlib's Fibonacci recurrence. "
                            + "Golden-word recognizability then gives an explicit bijection from "
                            + "two copies of the natural numbers to all indices: the branches are "
                            + "S(v) and 1+S(v)+v. Restricting that bijection to each exponent fiber "
                            + "and using Mathlib's cardinality-of-equivalence and cardinality-of-sum "
                            + "laws proves the equation without analytic convergence assumptions.")),
                    Paragraph(Text(
                        "Mathlib's general Rayleigh theorem for complementary Beatty sequences was "
                            + "checked during the prior-art search. The proof uses the already formalized "
                            + "golden substitution recognizability statements instead because they match "
                            + "the source's shifted indexing exactly and also supply the exponent identities."))),
                DescribeRole.Theorem))));
}
