using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GroupWords;

internal sealed class UniformCommutatorNilpotenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform vanishing depth for commutator words of generators forces their "
        + "generated subgroup to be nilpotent.",
        H("Uniform Commutator Words and Nilpotence"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-commutator-nilpotence"),
            DeclarationHandle.Create("D5/S3/Combinatorics/GroupWords/UniformCommutatorNilpotence.result"),
            H("From generators to the whole generated subgroup"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Geometry/frenzymath2026poincarelibrary")),
            Blocks(
                Paragraph(Text(
                    "G is any group in any type universe, S any subset of G, and N any "
                    + "natural number. The predicate vanish(G,S,N) means: for every list "
                    + "l of exactly N elements of S and every b in S, start at z=b and "
                    + "process the list from left to right, replacing z by a*z*a inverse*z inverse "
                    + "at each letter a. The final element is one. The same N works for every "
                    + "such list and root; a root-dependent or word-dependent depth is not sufficient.")),
                Paragraph(Text(
                    "Generated(G,S) is the actual subgroup closure of S with its induced "
                    + "group structure. Nilpotent means that its upper central series reaches "
                    + "the whole subgroup after finitely many steps. S need not be finite, "
                    + "symmetric, normal, or contain one. The empty set and N=0 remain in scope.")),
                Paragraph(Text(
                    "Work inside the generated subgroup H and pull S back through its inclusion "
                    + "to a set T generating all of H. Induct on n to show that a root annihilated "
                    + "by every length-n T word belongs to the nth upper central subgroup. At zero "
                    + "the empty word forces the root to be one. At a successor, prefix any "
                    + "generator a to a word: the induction hypothesis puts the commutator of "
                    + "a with the root into the preceding upper central subgroup.")),
                Paragraph(Text(
                    "In the quotient by that normal upper central subgroup, every generator "
                    + "therefore commutes with the root image. Pulling back the centralizer of "
                    + "that image gives a subgroup containing T, hence all of H. Thus the root "
                    + "commutes with every element modulo the preceding term and belongs to "
                    + "the next term. This promotes a condition on generators to the whole group; "
                    + "it does not assume that S is normal or closed under commutators.")),
                Paragraph(Text(
                    "Inclusion into G intertwines each commutator and the complete list fold. "
                    + "The stated uniform vanishing premise then puts every element of T into "
                    + "the Nth upper central subgroup. Since T generates H, that term is all "
                    + "of H, proving nilpotence. The premise itself must be established for any "
                    + "geometric application; this theorem does not supply a Lorentz matrix "
                    + "estimate, a hyperbolic deck representation, a Margulis bound, or rigidity."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula g = F.Id("G"), s = F.Id("S"), n = F.Id("N");
        return Disp(ForAll("G", F.Id("Typeu"),
            Implies(Call("Group", g), ForAll("S", Call("Sets", g),
                ForAll("N", F.Id("Nat"), Implies(Call("vanish", g, s, n),
                    Call("Nilpotent", Call("Generated", g, s))))))));
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
