using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ResidueCoding;

internal sealed class ElementReductionCoarseInvariantDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ResidueCoding/ElementReductionCoarseInvariant."
            + "element_reduction_coarse_invariant_fork";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entrywise reduction separates two integral matrices at every prime while trace and "
            + "characteristic polynomial merge the same reductions.",
        H("Element Reduction and Coarse Invariants"),
        Blocks(Describe.Lean(
            DescribeId.Create("element-reduction-coarse-invariant-fork"),
            DeclarationHandle.Create(Declaration),
            H("Prime reduction can separate what coarse invariants merge"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take the two-by-two integral zero matrix A and the matrix N whose only "
                        + "nonzero entry is one in row zero and column one. These are distinct "
                        + "global integral objects.")),
                Paragraph(Text(
                    "For every prime p, entrywise reduction modulo p still distinguishes A "
                        + "from N because the distinguished entry remains one.")),
                Paragraph(Text(
                    "On those same reduced matrices, both traces are zero and both characteristic "
                        + "polynomials are X squared. The positive separation and the coarse "
                        + "collision therefore use one shared construction at every prime."))),
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
        Formula zeroMatrix = F.Id("A");
        Formula nilpotent = F.Id("N");
        Formula prime = F.Id("p");
        Formula integralZero = Call("zeroMatrix", D(2), F.Id("Z"));
        Formula integralNilpotent =
            Call("single", D(2), D(0), D(1), D(1), F.Id("Z"));
        Formula reducedZero = Call("reduction", prime, zeroMatrix);
        Formula reducedNilpotent = Call("reduction", prime, nilpotent);

        return Disp(new Formula.Aligned([
            Seq(zeroMatrix, Sp, Eq, Sp, integralZero, Comma, Sp,
                nilpotent, Sp, Eq, Sp, integralNilpotent, Comma),
            Seq(NotEqual(zeroMatrix, nilpotent), Sp, Land),
            Seq(Forall, Sp, prime, Sp, InMacro, Sp, F.Id("Primes"), Comma),
            Seq(NotEqual(reducedZero, reducedNilpotent), Sp, Land),
            Seq(Call("trace", reducedZero), Sp, Eq, Sp,
                Call("trace", reducedNilpotent), Sp, Land),
            Seq(Call("charpoly", reducedZero), Sp, Eq, Sp,
                Call("charpoly", reducedNilpotent), Dot),
        ]));
    }
}
