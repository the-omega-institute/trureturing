using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class GoldenFiberCapacityPairsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden fiber capacities are the adjacent integer pairs four-five and two-three.",
        H("Golden Fiber Capacity Pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-fiber-capacity-pairs"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/GoldenFiberCapacityPairs.golden_fiber_capacity_pairs"),
                H("The golden fiber capacities are exact adjacent pairs"),
                StatementSource.FromAuthor(Disp(Seq(
                    OpenBrace,
                    Lfloor, Varphi, Caret, Grp(D(3)), Rfloor, Comma, Sp,
                    Operatorname, Grp(F.Id("ceil")), Open,
                    Varphi, Caret, Grp(D(3)), Close,
                    CloseBrace, Sp, Eq, Sp, OpenBrace, D(4), Comma, Sp, D(5), CloseBrace,
                    Sp, Land, Sp,
                    OpenBrace,
                    Lfloor, Varphi, Caret, Grp(D(2)), Rfloor, Comma, Sp,
                    Operatorname, Grp(F.Id("ceil")), Open,
                    Varphi, Caret, Grp(D(2)), Close,
                    CloseBrace, Sp, Eq, Sp, OpenBrace, D(2), Comma, Sp, D(3), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The declaration packages the four frozen floor and ceiling values into "
                        + "the two finite-set equalities stated by the source. It directly reuses "
                        + "golden_power_floor_ceil_pairs and does not reprove any rounding fact.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched for floor and ceiling APIs, golden-ratio "
                        + "identities, and an exact finite-set pair theorem. Generic APIs and the "
                        + "identities were present, but no declaration states these assembled pairs.")),
                    Paragraph(Text(
                        "This deposit closes only the explicit capacity-pair equalities in source "
                        + "proposition 6.42, clause 2. The support interval, Sturmian distribution, "
                        + "and asymptotic frequency assertions remain outside this declaration."))),
                DescribeRole.Theorem))));
}
