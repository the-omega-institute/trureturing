using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class KleinFourFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/KleinFourFactorization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/alcalaarroyo2026kleinfour");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H = Multiplicative(ZMod(2) x ZMod(2)), with alphabet Bool. Configurations are all functions H -> Bool, and the right shift is rho_g(x)(h) = x(h g). The predicates IsCA, IsLazy and IsInvertibleCA are the existing local-rule predicates: a lazy rule has exactly one active exceptional pattern on any finite neighborhood containing 1. Let W_n be the set of configurations with exactly n true cells, C the two constants, O(x) the shift orbit of x, and c_b the constant with value b. Write w_false = 1 and w_true = 3. The public theorem below transports the structural proof by E. Alcala-Arroyo, A. Castillo-Ramirez, H. Ma and W. Zhang (public supplement v1.1.0, DOI 10.5281/zenodo.23280244) to this configuration space.",
        H("Membership in the lazy and invertible generated submonoid"),
        Blocks(Describe.Lean(DescribeId.Create("kleinfour-actual-membership"),
            DeclarationHandle.Create(Prefix + "membership_iff"),
            H("The structural criterion on actual configurations"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("U comprises all maps satisfying IsInvertibleCA and L all maps satisfying IsLazy. The generated submonoid includes the identity, represented by the empty word. A common image W_(w_b) in the antecedent is a free orbit; images that are constant or two-point orbits do not activate this condition. The consequent states equality of the image of C union O(x) with the singleton {c_b}, where O(x) has two points.")),
                Paragraph(Text("The seven-orbit representation is bijective with all configurations. Sending false and true to 0 and 1 in each group coordinate identifies xor with multiplication in H and carries the model action to the right shift. Conjugation identifies every model equivariant map with a cellular automaton; conversely every cellular automaton commutes with shifts and gives a model equivariant map. On this finite group every equivariant map has a full-neighborhood local rule. The lazy generators correspond in both directions by transporting the neighborhood and exceptional pattern, extending that pattern arbitrarily outside its neighborhood. Bijectivity gives an equivariant inverse and hence agrees with IsInvertibleCA. These identities transport both inclusions of the generated closure.")),
                Paragraph(Text("For the reverse implication, a nonmerging map factors into elementary collapses, independent lower-stratum actions and a unit extending the partial permutation on the free strata. A merging map with the stated witness factors through B_s, followed and preceded by nonmerging maps. With k_s the nonidentity group element selected by the index s, the transported coordinate rule is B_s(x)(g) = x(g) and not x(g k_s). Every factor belongs to the full lawful generating family. Weight-one and weight-three configurations are exactly the two model free strata, and the three model pair strata exhaust all two-point shift orbits. No fixed cardinality of a generated monoid, shortest-word result or lazy-only sufficient condition is asserted."))),
            DescribeRole.Theorem)), []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Image(Formula set) => Seq(F.Id("T"), OpenBracket, set, CloseBracket);
    private static Formula W(Formula n) => new Formula.Subscript(F.Id("W"), n);
    private static Formula Statement()
    {
        Formula b = F.Id("b"), x = F.Id("x");
        Formula wb = new Formula.Subscript(F.Id("w"), b);
        Formula merge = Seq(Exists, Sp, b, Sp, InMacro, Sp, F.Id("Bool"), Comma, Sp,
            And(Eq(Image(W(D(1))), W(wb)), Eq(Image(W(D(3))), W(wb))));
        Formula witness = Seq(Exists, Sp, x, Sp, InMacro, Sp, new Formula.Power(F.Id("Bool"), F.Id("H")),
            Comma, Sp, b, Sp, InMacro, Sp, F.Id("Bool"), Comma, Sp,
            And(Eq(Seq(Bar, Call("O", x), Bar), D(2)),
                Eq(Image(Seq(F.Id("C"), Sp, Cup, Sp, Call("O", x))),
                    Seq(OpenBrace, new Formula.Subscript(F.Id("c"), b), CloseBrace))));
        return Seq(Forall, Sp, F.Id("T"), Sp, InMacro, Sp,
            Call("End", new Formula.Power(F.Id("Bool"), F.Id("H"))), Comma, Sp,
            Call("IsCA", F.Id("T")), Sp, Implies, Sp, Open,
            new Formula.Logic(Mem(F.Id("T"), Call("closure", Seq(F.Id("U"), Sp, Cup, Sp, F.Id("L")))),
                FormulaLogicOperator.Iff, Seq(Open,
                    new Formula.Logic(Seq(Open, merge, Close), FormulaLogicOperator.Implies, witness), Close)), Close);
    }
}
