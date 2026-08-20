using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class DynamicsResidualQuotientUniqueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The orthogonal residual of an iterated observable closure is invariant and has a unique quotient descent.",
        H("Unique Descent on the Final Orthogonal Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjoint-observable-residual-has-unique-descent"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/DynamicsResidualQuotientUnique."
                        + "dynamics_residual_invariant_and_unique_quotient"),
                H("The final orthogonal residual is invariant and has a unique quotient descent"),
                StatementSource.FromAuthor(ResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The visible space is constructed from every forward iterate of the "
                            + "adjoint observable map K applied to the source visible subspace W. "
                            + "The residual is its orthogonal complement.")),
                    Paragraph(Text(
                        "The adjoint pairing transfers orthogonality through Phi, and the public "
                            + "existence-unique clause states that exactly one linear map on the "
                            + "quotient satisfies the projection law.")),
                    Paragraph(Text(
                        "Repository search found no exact theorem packaging the invariant residual "
                            + "with unique quotient descent. Pinned Mathlib supplies and is applied "
                            + "through Submodule.mem_orthogonal', Submodule.liftQ, "
                            + "Submodule.liftQ_apply, Submodule.Quotient.mk_eq_zero, and "
                            + "Submodule.mkQ_surjective."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula ScalarTypeclass(string name, Formula scalar, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Underscore, Grp(scalar),
            Open, argument, Close, CloseBracket);

    private static Formula LinearMap(Formula scalar, Formula source, Formula target) =>
        Seq(Operatorname, Grp(F.Id("LinearMap")), Underscore, Grp(scalar),
            Open, source, Sp, To, Sp, target, Close);

    private static Formula ResidualFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = F.Id("V");
        Formula map = F.Id("K");
        Formula evolution = F.Id("Phi");
        Formula visibleSeed = F.Id("W");
        Formula visible = Call("observableClosureUnique", map, visibleSeed);
        Formula residual = Seq(visible, Caret, Grp(Perp));
        Formula x = F.Id("x");
        Formula a = F.Id("a");
        Formula innerLeft = Call("inner", real, Apply(evolution, x), a);
        Formula innerRight = Call("inner", real, x, Apply(map, a));
        Formula quotient = Call("Quotient", residual);
        Formula induced = F.Id("induced");
        Formula other = F.Id("other");
        Formula inducedLaw = Seq(
            Forall, Sp, x, Comma, Sp,
            Apply(induced, Call("mkQ", residual, x)), Sp, Eq, Sp,
            Call("mkQ", residual, Apply(evolution, x)));
        Formula otherLaw = Seq(
            Forall, Sp, x, Comma, Sp,
            Apply(other, Call("mkQ", residual, x)), Sp, Eq, Sp,
            Call("mkQ", residual, Apply(evolution, x)));

        return Disp(Seq(
            Forall, Sp, space, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Typeclass("NormedAddCommGroup", space), Comma, Sp,
            ScalarTypeclass("InnerProductSpace", real, space), Comma, Sp,
            ScalarTypeclass("FiniteDimensional", real, space), Comma, Esc,
            map, Colon, Sp, LinearMap(real, space, space), Comma, Sp,
            evolution, Colon, Sp, LinearMap(real, space, space), Comma, Sp,
            visibleSeed, Colon, Sp, Call("Submodule", real, space), Comma, Esc,
            Forall, Sp, x, Comma, Sp, a, Comma, Sp,
            innerLeft, Sp, Eq, Sp, innerRight, Sp, Rightarrow, Esc,
            Open,
            Forall, Sp, x, Comma, Sp, x, Sp, InMacro, Sp, residual,
            Comma, Sp, Apply(evolution, x), Sp, InMacro, Sp, residual,
            Close, Sp, Land, Sp, RowBreak,
            Exists, Sp, induced, Colon, Sp, LinearMap(real, quotient, quotient), Comma, Sp,
            Open, inducedLaw, Sp, Land, Sp,
            Forall, Sp, other, Colon, Sp, LinearMap(real, quotient, quotient), Comma, Sp,
            otherLaw, Sp, Rightarrow, Sp, other, Sp, Eq, Sp, induced,
            Close, Dot));
    }
}
