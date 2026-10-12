using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.NumberTheory.ModularForms;

internal sealed class FiniteCharacterOrthogonalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef LidlNiederreiter =
        LibraryNoteRef.Create("D5/L/ArithSums/lidlniederreiter1997finitefields");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nontrivial multiplicative character on a finite group has zero total sum, and a unitary character has one unit of norm-square mass per group element.",
        H("Finite Character Orthogonality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nontrivial-finite-character-sum-is-zero"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality."
                        + "nontrivial_character_sum_eq_zero"),
                H("A nontrivial finite-group character sums to zero"),
                StatementSource.FromAuthor(OrthogonalityFormula()),
                AssessedProvenance.FromLiterature(LidlNiederreiter),
                Blocks(
                    Paragraph(Text(
                        "For a finite group G and a multiplicative character χ that is not the trivial character, the sum of χ over G vanishes.")),
                    Paragraph(Text(
                        "Choose a with χ(a) ≠ 1. Left translation by a permutes G, so multiplying the sum by χ(a) leaves it unchanged. Cancellation in ℂ then forces the sum to be zero.")),
                    Paragraph(Text(
                        "This is the finite algebraic orthogonality input used in Gauss-sum and Hasse--Davenport arguments. It does not supply the analytic Hecke action or the Hasse--Davenport product formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-character-norm-square-sum-is-cardinality"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality."
                        + "unitary_character_norm_sq_sum_eq_card"),
                H("A unitary character has exact norm-square mass"),
                StatementSource.FromAuthor(NormFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the character takes values on the unit circle, every summand has squared norm one, so the total norm-square mass is exactly the finite group cardinality.")),
                    Paragraph(Text(
                        "The unit-modulus hypothesis is explicit: an arbitrary monoid hom into ℂ need not be unitary. This normalization is the one consumed by the standard Gauss-sum norm calculation."))),
                DescribeRole.Proposition)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Arith/FiniteFieldQuadraticCharacterSum"))]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula OrthogonalityFormula()
    {
        Formula group = F.Id("G");
        Formula character = F.Id("chi");
        Formula element = F.Id("g");
        Formula monoidHom = Call("MonoidHom", group, F.Id("Complex"));
        Formula sum = Seq(Sum, Sp, element, InMacro, Sp, group, Sp,
            character, Open, element, Close);
        return Disp(Seq(
            Forall, Sp, group, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Call("Group", group), Sp, Land, Sp, Call("Fintype", group), Comma, Esc,
            character, Colon, Sp, monoidHom, Comma, Sp,
            character, Sp, Neq, Sp, D(1), Sp, Rightarrow, Sp,
            sum, Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula NormFormula()
    {
        Formula group = F.Id("G");
        Formula character = F.Id("chi");
        Formula element = F.Id("g");
        Formula sum = Seq(Sum, Sp, element, InMacro, Sp, group, Sp,
            new Formula.Norm(Seq(character, Open, element, Close)), Caret, D(2));
        return Disp(Seq(
            Forall, Sp, group, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Call("Group", group), Sp, Land, Sp, Call("Fintype", group), Comma, Esc,
            character, Colon, Sp, Call("MonoidHom", group, F.Id("Complex")), Comma, Esc,
            Forall, Sp, element, Colon, Sp, group, Comma, Sp,
            new Formula.Norm(Seq(character, Open, element, Close)), Eq, D(1), Sp,
            Rightarrow, Sp, sum, Sp, Eq, Sp, Call("card", group), Dot));
    }
}
