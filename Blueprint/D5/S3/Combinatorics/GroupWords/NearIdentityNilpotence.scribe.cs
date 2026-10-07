using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GroupWords;

internal sealed class NearIdentityNilpotenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive identity isolation gap in a normed ring representation forces the "
        + "subgroup generated near one to be nilpotent.",
        H("Near Identity Generators and Nilpotence"),
        Blocks(Describe.Lean(
            DescribeId.Create("near-identity-nilpotence"),
            DeclarationHandle.Create("D5/S3/Combinatorics/GroupWords/NearIdentityNilpotence.result"),
            H("Contraction supplies the uniform commutator depth"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Geometry/frenzymath2026poincarelibrary")),
            Blocks(
                Paragraph(Text(
                    "G is any group and R any normed ring, in independent type universes. "
                    + "The ring norm is submultiplicative and its identity has norm one. "
                    + "The map f is a group homomorphism from G to the units of R. "
                    + "Gap(G,R,f,e) means that e is a positive real number and, for every "
                    + "g in G, norm(f(g)-one) less than e implies g=one. This is an actual "
                    + "isolation premise, not merely continuity or a chosen topology on G.")),
                Paragraph(Text(
                    "Near(G,R,f) consists of every g with norm(f(g)-one) at most 1/16. "
                    + "Generated(G,Near) is its actual subgroup closure inside G. "
                    + "Neither finite generation, normality of Near, nor completeness "
                    + "of R is required. Nilpotence and the uniform commutator depth "
                    + "are conclusions, not hypotheses.")),
                Paragraph(Text(
                    "For a unit u within 1/16 of one, rewrite its inverse as one minus "
                    + "(u-one) times its inverse. The triangle inequality and "
                    + "submultiplicativity bound the inverse norm by two. The normed "
                    + "ring commutator estimate then shows that commutation with a "
                    + "near generator contracts a near root's distance from one by "
                    + "at most one half. The new root stays within the same near region.")),
                Paragraph(Text(
                    "Induction on arbitrary lists bounds the iterated commutator norm "
                    + "by (1/2) to the list length times the initial root norm. "
                    + "Geometric convergence supplies one natural depth N with "
                    + "(1/2)^N/16 less than the given positive gap. Consequently every "
                    + "length-N list of near generators annihilates every near root. "
                    + "The uniform generator word criterion promotes this conclusion "
                    + "to nilpotence of the entire generated subgroup.")),
                Paragraph(Text(
                    "The isolation gap has to be proved for each application. "
                    + "This theorem does not construct a hyperbolic covering, a "
                    + "Lorentz representation or a geometric small displacement "
                    + "bound. It alone establishes neither virtual nilpotence of "
                    + "small displacement groups nor Mostow-Prasad rigidity."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula g = F.Id("G"), r = F.Id("R"), f = F.Id("f"), e = F.Id("e");
        return Disp(ForAll("G", F.Id("Typeu"), ForAll("R", F.Id("Typev"),
            Implies(Call("Group", g), Implies(Call("NormedRingWithNormOne", r),
                ForAll("f", Call("GroupHom", g, Call("Units", r)),
                    ForAll("e", F.Id("Real"), Implies(Call("Gap", g, r, f, e),
                        Call("Nilpotent", Call("Generated", g,
                            Call("Near", g, r, f)))))))))));
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
