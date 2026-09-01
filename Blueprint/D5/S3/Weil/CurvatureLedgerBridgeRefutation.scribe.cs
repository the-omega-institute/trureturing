using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class CurvatureLedgerBridgeRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two frozen-definition toy readouts refute a globally normalized curvature-ledger measure bridge.",
        H("Curvature-Ledger Bridge Refutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-curvature-atom"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.unitCurvatureAtom"),
                H("Literal unit-multiplicity curvature atom"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a spectral point rho, this specialization retains exactly the frozen curvature " +
                    "location -Im(rho) + i(Re(rho) - 1/2) and the unit-multiplicity mass 2 pi. " +
                    "It introduces no calibration or alternate support map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-deficit-pair"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.zeroDeficitPair"),
                H("Frozen mirror-pair deficit readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The paired deficit measure is the sum of the already frozen zeroDeficitMeasure at rho " +
                    "and at mirror(rho). Each atom remains supported at its original zero address."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-curvature-readout"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.first_curvature_readout"),
                H("First curvature readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("unitCurvatureAtom")), Open, Frac, Grp(D(3)), Grp(D(4)), Close,
                    Eq, Operatorname, Grp(F.Id("ofReal")), Open, D(2), Pi, Close,
                    Operatorname, Grp(F.Id("dirac")), Open, Frac, Grp(F.Id("i")), Grp(D(4)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the W-B1 zero pair {3/4, 1/4}, only the right zero enters the frozen curvature sum. " +
                    "Its upperPoint is i/4 and its unit-multiplicity mass is 2 pi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-deficit-readout"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.first_deficit_readout"),
                H("First deficit readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("zeroDeficitPair")), Open, Frac, Grp(D(3)), Grp(D(4)), Close,
                    Eq, Frac, Grp(D(1)), Grp(D(3, 2)), Operatorname, Grp(F.Id("dirac")), Open,
                    Frac, Grp(D(3)), Grp(D(4)), Close, Plus,
                    Frac, Grp(D(1)), Grp(D(3, 2)), Operatorname, Grp(F.Id("dirac")), Open,
                    Frac, Grp(D(1)), Grp(D(4)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen address gives zeroAddressedScaling = 1/8 at both zeros, so the selected " +
                    "second variation is 1/32 at each. The measure is supported at 3/4 and 1/4, not at i/4, " +
                    "and its total mass is 1/16."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-curvature-readout"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.second_curvature_readout"),
                H("Second curvature readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("unitCurvatureAtom")), Open, D(1), Close,
                    Eq, Operatorname, Grp(F.Id("ofReal")), Open, D(2), Pi, Close,
                    Operatorname, Grp(F.Id("dirac")), Open, Frac, Grp(F.Id("i")), Grp(D(2)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the distinct displacement pair {1, 0}, the right-zero curvature atom moves to i/2 " +
                    "while retaining the same unit-multiplicity mass 2 pi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-deficit-readout"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.second_deficit_readout"),
                H("Second deficit readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("zeroDeficitPair")), Open, D(1), Close,
                    Eq, Frac, Grp(D(1)), Grp(D(2)), Operatorname, Grp(F.Id("dirac")), Open, D(1), Close,
                    Plus, Frac, Grp(D(1)), Grp(D(2)), Operatorname, Grp(F.Id("dirac")), Open, D(0), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At displacement one half, zeroAddressedScaling = 1/2 and the selected second variation " +
                    "is 1/2. The two deficit atoms therefore remain at 1 and 0 with total mass 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-global-mass-normalization"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.no_global_mass_normalization"),
                H("No global mass normalization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Exists, Sp, F.Id("c"), InMacro, Mathbb, Grp(F.Id("R")), Underscore, Grp(F.Id("ge0")),
                    Comma, Sp, F.Id("c"), D(1, 6), Caret, Grp(Minus, D(1)), Eq,
                    D(2), Operatorname, Grp(F.Id("ofReal")), Open, Pi, Close,
                    Sp, Land, Sp, F.Id("c"), Eq, D(2), Operatorname, Grp(F.Id("ofReal")), Open, Pi, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A global scalar would have to send total deficit mass 1/16 to 2 pi in the first example " +
                    "and total deficit mass 1 to 2 pi in the second. Positivity of pi makes those equations " +
                    "incompatible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("curvature-ledger-bridge-refuted"),
                DeclarationHandle.Create("D5/S3/Weil/CurvatureLedgerBridgeRefutation.curvature_ledger_bridge_refuted"),
                H("W-B3 bridge verdict"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Exists, Sp, F.Id("c"), InMacro, Mathbb, Grp(F.Id("R")), Underscore, Grp(F.Id("ge0")),
                    Comma, Sp, F.Id("c"), Operatorname, Grp(F.Id("zeroDeficitPair")), Open,
                    Frac, Grp(D(3)), Grp(D(4)), Close, Eq,
                    Operatorname, Grp(F.Id("unitCurvatureAtom")), Open, Frac, Grp(D(3)), Grp(D(4)), Close,
                    Sp, Land, Sp, F.Id("c"), Operatorname, Grp(F.Id("zeroDeficitPair")), Open, D(1), Close,
                    Eq, Operatorname, Grp(F.Id("unitCurvatureAtom")), Open, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Verdict: bridge-refuted. Applying a hypothetical common measure scalar to the universal " +
                    "set would imply the two incompatible total-mass equations. Independently, the exact " +
                    "readouts expose a support mismatch in both examples: curvature lives at i/4 or i/2, " +
                    "whereas deficit remains at the original real zero pair."))),
                DescribeRole.Theorem)
        )));
}
