using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class PrimePowerTensorTowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/ObserverMemory/PrimePowerTensorTower",
            "A finite window full-matrix algebra is the tensor product of all of its prime-power full-matrix factors."),
        H("Prime-Power Tensor Tower of a Finite Window Algebra"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-window-matrix-algebra-splits-into-all-prime-power-factors"),
                H("A finite window matrix algebra splits into all prime-power factors"),
                LeanTheorem(
                    "D5/S3/ObserverMemory/PrimePowerTensorTower.prime_power_tensor_factor_decomposition"),
                FactorizationFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let M be a nonzero finite window cardinality. The canonical ZMod.equivPi " +
                        "ring equivalence identifies its address type with the dependent product " +
                        "of ZMod (p^(M.factorization p)) over p in M.primeFactors.")),
                    Paragraph(Text(
                        "Reindexing both matrix coordinates gives the full matrix algebra on that " +
                        "dependent product. The finite Pi tensor product of the factor matrix-unit " +
                        "bases is carried to the global matrix-unit basis, and the map preserves " +
                        "multiplication. This yields a complex algebra equivalence with the actual " +
                        "finite tensor family, not merely an index reordering or a two-factor " +
                        "clock-and-shift identity.")))))));

    private static Formula FactorizationFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Gt, F.D(0), Comma, Sp,
        F.Id("M"), Underscore, Grp(F.Id("M")),
        Open, Mathbb, Grp(F.Id("C")), Close,
        Sp, Sim, Underscore, Grp(Mathbb, Grp(F.Id("C"))), Sp,
        Operatorname, Grp(F.Id("Tensor")), Underscore, Grp(
            F.Id("p"), Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("primeFactors")), Open, F.Id("M"), Close),
        Sp,
        F.Id("M"), Underscore, Grp(
            F.Id("p"), Caret, Grp(
                Operatorname, Grp(F.Id("factorization")),
                Open, F.Id("M"), Comma, F.Id("p"), Close)),
        Open, Mathbb, Grp(F.Id("C")), Close, Dot));
}
