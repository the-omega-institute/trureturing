using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class ObservableAlgebraClosureDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite relation fibers and iterated pullbacks generate exactly the stable fiber algebra.",
        H("Stable Relations and Observable Algebra Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("iterated-pullbacks-equal-the-stable-fiber-algebra"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/ObservableAlgebraClosureDuality."
                        + "koopman_closure_eq_stable_fiber_algebra"),
                H("The iterated pullback algebra equals the stable fiber algebra"),
                StatementSource.FromAuthor(ClosureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The fiber star algebra is constructed from complex-valued functions "
                            + "constant on the source equivalence relation and closed under "
                            + "the pointwise star operation. The stable relation requires "
                            + "agreement after every finite iterate of the transition.")),
                    Paragraph(Text(
                        "The pullback star closure is generated from actual iterates of source-fiber "
                            + "functions. Finite separating indicators prove the reverse inclusion, "
                            + "so the target equality is derived rather than used as a definition.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no exact packaged theorem. "
                            + "The proof directly applies StarAlgebra.adjoin_le, "
                            + "StarAlgebra.subset_adjoin, StarSubalgebra.prod_mem, "
                            + "StarSubalgebra.sum_mem, Quotient.sound, and Quotient.exact."))),
                DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

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

    private static Formula ClosureFormula()
    {
        Formula y = F.Id("Y");
        Formula relation = F.Id("R");
        Formula transition = F.Id("tau");
        Formula relationType = Seq(y, Sp, To, Sp, y, Sp, To, Sp, F.Id("Prop"));
        Formula transitionType = Seq(y, Sp, To, Sp, y);
        Formula stable = Call("stableRelation", relation, transition);

        return Disp(Seq(
            Forall, Sp, y, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Finite", y), Comma, Sp,
            relation, Colon, Sp, relationType, Comma, Sp,
            transition, Colon, Sp, transitionType, Comma, Sp,
            Call("Equivalence", relation), Sp, Rightarrow, Sp,
            Call("koopmanClosure", relation, transition), Sp, Eq, Sp,
            Call("fiberStarAlgebra", stable), Dot));
    }
}
