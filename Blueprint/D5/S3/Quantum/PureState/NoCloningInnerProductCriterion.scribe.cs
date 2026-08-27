using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class NoCloningInnerProductCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact unitary cloning makes the input-state overlap idempotent.",
        H("No-Cloning Inner-Product Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-cloning-inner-product-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PureState/NoCloningInnerProductCriterion."
                        + "no_cloning_inner_product_criterion"),
                H("Clonable pure states are identical or orthogonal"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A complex linear isometric equivalence is assumed to clone two "
                            + "normalized vectors from the same normalized blank vector.")),
                    Paragraph(Text(
                        "Preservation of the tensor-product inner product makes their overlap "
                            + "equal to its square. Unit overlap identifies the normalized "
                            + "vectors, while the remaining idempotent value is zero."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula space = F.Id("H");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula tensor = Call("TensorProduct", complex, space, space);
        Formula unitary = Call("LinearIsometryEquiv", complex, tensor, tensor);
        Formula u = F.Id("U");
        Formula psi = F.Id("psi");
        Formula phi = F.Id("phi");
        Formula blank = F.Id("blank");
        Formula Tmul(Formula left, Formula right) =>
            Call("tmul", complex, left, right);
        Formula Apply(Formula function, Formula value) =>
            new Formula.Apply(function, [value]);
        Formula Inner(Formula left, Formula right) =>
            Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle,
                Underscore, Grp(complex));
        Formula NormOne(Formula value) =>
            Seq(Vert, Sp, value, Sp, Vert, Sp, Eq, Sp, D(1));

        Formula assumptions = Seq(
            Call("NormedAddCommGroup", space), Sp, Land, Sp,
            Call("InnerProductSpace", complex, space), Sp, Land, Sp,
            NormOne(psi), Sp, Land, Sp, NormOne(phi), Sp, Land, Sp,
            NormOne(blank), Sp, Land, Sp,
            Apply(u, Tmul(psi, blank)), Sp, Eq, Sp, Tmul(psi, psi), Sp, Land, Sp,
            Apply(u, Tmul(phi, blank)), Sp, Eq, Sp, Tmul(phi, phi));
        Formula overlap = Inner(phi, psi);
        Formula idempotent = Seq(
            overlap, Sp, Eq, Sp,
            overlap, Caret, Grp(D(2)));
        Formula alternative = Seq(
            phi, Sp, Eq, Sp, psi, Sp, Lor, Sp, overlap, Sp, Eq, Sp, D(0));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("H"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("U"), unitary),
                new Formula.BoundVariable(FormulaIdentifier.Create("psi"), space),
                new Formula.BoundVariable(FormulaIdentifier.Create("phi"), space),
                new Formula.BoundVariable(FormulaIdentifier.Create("blank"), space),
            ],
            new Formula.Logic(
                assumptions,
                FormulaLogicOperator.Implies,
                Seq(idempotent, Sp, Land, Sp, Open, alternative, Close))));
    }
}
