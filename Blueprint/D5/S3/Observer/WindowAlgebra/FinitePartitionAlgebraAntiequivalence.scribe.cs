using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WindowAlgebra;

internal sealed class FinitePartitionAlgebraAntiequivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite real partition algebras and their relations reconstruct each other.",
        H("Finite Partition Algebra Antiequivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-partition-algebra-antiequivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraAntiequivalence."
                        + "finite_partition_algebra_antiequivalence"),
                H("Relations and real partition algebras reconstruct each other"),
                StatementSource.FromAuthor(AntiequivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be finite and R an equivalence relation. The algebra associated "
                            + "to R is constructed as the real functions constant on every "
                            + "R-class. Its agreement relation recovers R because an indicator "
                            + "of either class separates every nonrelated pair.")),
                    Paragraph(Text(
                        "Conversely, let A be a real function subalgebra. Agreement under all "
                            + "members of A defines a relation independently of the target "
                            + "algebra. Finite products of normalized separating functions put "
                            + "each relation-class indicator in A; a finite quotient expansion "
                            + "then expresses every relation-constant function as a member of A.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no exact theorem on the "
                            + "real carrier. The nearby observable-algebra theorem uses complex "
                            + "star subalgebras, so only its finite indicator proof pattern is "
                            + "adapted here; no complex-carrier statement is used as coverage."))),
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

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula AntiequivalenceFormula()
    {
        Formula state = F.Id("X");
        Formula relation = F.Id("R");
        Formula algebra = F.Id("A");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula algebraOfRelation = Subscript(algebra, relation);
        Formula relationOfAlgebra = Subscript(relation, algebra);
        Formula relationReconstruction = Seq(
            Subscript(relation, algebraOfRelation), Sp, Eq, Sp, relation);
        Formula algebraReconstruction = Seq(
            Subscript(algebra, relationOfAlgebra), Sp, Eq, Sp, algebra);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, relation, Comma, Sp, algebra, Comma, Esc,
            Call("Finite", state), Sp, Land, Sp,
            Call("Equivalence", relation), Sp, Land, Esc,
            algebra, Sp, InMacro, Sp,
            Call("Subalgebra", real, Seq(state, Sp, To, Sp, real)), Sp,
            Rightarrow, Esc,
            relationReconstruction, Sp, Land, Sp, algebraReconstruction, Dot));
    }
}
