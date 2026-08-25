using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ResidueCoding;

internal sealed class RetainedResidueRecoveryCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion."
            + "retained_residue_recovery_iff_product_capacity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retained coprime residue coordinates recover a bounded state exactly when their "
            + "product has sufficient capacity.",
        H("Retained Residue Recovery Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("retained-residue-recovery-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Retained residues are injective exactly at product capacity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let R be the finite family of retained coordinates. Each retained "
                        + "modulus is positive, and distinct retained moduli are coprime.")),
                Paragraph(Text(
                    "The observation is the canonical dependent joint readout whose ith "
                        + "coordinate reduces a bounded natural state modulo the ith modulus.")),
                Paragraph(Text(
                    "Injectivity forces the state-space cardinality not to exceed the product "
                        + "of the output cardinalities. Conversely, the finite-family Chinese "
                        + "remainder equivalence identifies equal residue words modulo the "
                        + "product, and the capacity bound makes the representatives equal."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula retained = F.Id("R");
        Formula moduli = F.Id("m");
        Formula capacity = F.Id("K");
        Formula index = F.Id("i");
        Formula state = F.Id("x");
        Formula stateSpace = new Formula.Subscript(F.Id("X"), capacity);
        Formula modulusAt = new Formula.Subscript(moduli, index);
        Formula residueAt = Seq(
            state, Sp, Operatorname, Grp(F.Id("mod")), Sp, modulusAt);
        Formula coordinateReadout = Seq(
            index, Sp, Mapsto, Sp, state, Sp, Mapsto, Sp, residueAt);
        Formula retainedProduct = Seq(
            Prod, Underscore, Grp(index, Sp, InMacro, Sp, retained), Sp, modulusAt);
        Formula positive = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, retained, Comma, Sp,
            D(0), Sp, Lt, Sp, modulusAt);
        Formula injective = Call(
            "Injective",
            Seq(
                Call("jointReadout", coordinateReadout),
                Colon, Sp, stateSpace, Sp, To, Sp,
                Prod, Underscore, Grp(index, Sp, InMacro, Sp, retained), Sp,
                Call("ZMod", modulusAt)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, retained, Comma, Sp, moduli, Comma, Sp, capacity, Comma,
            RowBreak, Grp(),
            Call("Finite", retained), Sp, Land, Sp,
            Open, positive, Close, Sp, Land, Sp,
            Call("PairwiseCoprime", moduli), Sp, Rightarrow,
            RowBreak, Grp(),
            injective, Sp, Iff, Sp,
            capacity, Sp, Leq, Sp, retainedProduct, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
