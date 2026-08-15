using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class GNSExpectationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive functional evaluates a star-square as the squared length of its pre-GNS vector.",
        H("GNS Expectation as Squared Length"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-functional-expectation-is-a-pre-gns-norm-square"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/GNSExpectation.expectation_eq_preGNS_norm_sq"),
                H("Positive-functional expectation is a pre-GNS norm square"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("NonUnitalCStarAlgebra")),
                    Open, F.Id("A"), Close, CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("PartialOrder")),
                    Open, F.Id("A"), Close, CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("StarOrderedRing")),
                    Open, F.Id("A"), Close, CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("omega"), InMacro, Sp, Operatorname,
                    Grp(F.Id("PositiveLinearMap")), Open, F.Id("A"), Comma,
                    Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
                    Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("A"), Comma, Esc,
                    F.Id("omega"), Open, F.Id("x"), Caret, Grp(Star), Sp,
                    F.Id("x"), Close, Eq,
                    Vert, Operatorname, Grp(F.Id("toPreGNS")), Open,
                    F.Id("omega"), Comma, F.Id("x"), Close, Vert,
                    Caret, Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be a partially ordered non-unital C-star algebra whose order is compatible with its star structure. For every positive complex linear functional omega and element x, omega applied to star x times x is the squared norm of the pre-GNS vector represented by x.")),
                    Paragraph(Text(
                        "The proof is the exact specialization and symmetric orientation of Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal.PositiveLinearMap.preGNS_norm_sq. No second proof of the GNS construction is introduced.")),
                    Paragraph(Text(
                        "This declaration closes only the GNS squared-length clause of the source atom. It makes no claim about the atom's Tsirelson decomposition, two-source classification, or narrative synthesis."))),
                DescribeRole.Theorem))));
}
