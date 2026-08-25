using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Midslope;

internal sealed class TwoNewExactValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two half-parameter midslope curvatures have exact logarithmic values and affine relations.",
        H("Two New Midslope-Curvature Values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-new-midslope-curvature-values"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Midslope/TwoNewExactValues.two_new_exact_values"),
                H("The half-parameter values and their affine relations"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Open, Frac, Grp(D(1)), Grp(D(2)), Close, Eq,
                    Frac,
                    Grp(Seq(D(5), Minus, D(1, 2), Sp, Log, Sp, D(2))),
                    Grp(D(6)), Sp, Land, Sp,
                    F.Id("J"), Open, Minus, Frac, Grp(D(1)), Grp(D(2)), Close, Eq,
                    Frac,
                    Grp(Seq(D(1), Minus, D(2), Sp, Log, Sp, D(2))),
                    Grp(D(2)), Sp, Land, Sp,
                    F.Id("J"), Open, Frac, Grp(D(1)), Grp(D(2)), Close, Eq,
                    Frac, Grp(D(5)), Grp(D(6)), Sp,
                    F.Id("J"), Open, D(0), Close, Plus,
                    Frac, Grp(D(1)), Grp(D(3)), Sp,
                    F.Id("J"), Open, D(1), Close, Sp, Land, Sp,
                    F.Id("J"), Open, Minus, Frac, Grp(D(1)), Grp(D(2)), Close, Eq,
                    Frac,
                    Grp(Seq(F.Id("J"), Open, D(0), Close)),
                    Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof applies the frozen exact half-power evaluation, the affine "
                            + "identity, and the negative-half relation. The explicit negative-half "
                            + "value follows by substituting the frozen geometric-mean value.")),
                    Paragraph(Text(
                        "All four clauses concern the canonical midslope-curvature integrals; no "
                            + "claim about other parameters is included."))),
                DescribeRole.Theorem))));
}
