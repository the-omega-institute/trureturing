using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class MiaoFukaiHamiltoniansDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/MiaoFukaiHamiltonians.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/miaofukai2026novel");

    private static readonly Formula L = F.Id("L");
    private static readonly Formula B = F.Id("b");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula HMin = F.Id("h");
    private static readonly Formula Delta = F.Id("d");
    private static readonly Formula Mu = F.Id("m");
    private static readonly Formula V = F.Id("v");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Complex = Seq(Mathbb, Grp(F.Id("C")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One odd-deficit sector of the periodic ladder contains an explicitly counted family of singleton components.",
        H("Singleton charge components in the periodic Rydberg ladder"),
        Blocks(
            Paragraph(Text("The rows and columns are indexed by labelled blockade words. The restricted graph has one vertex per word of the specified charge. Distinct vertices are adjacent when the Hamiltonian entry in either direction is nonzero. PreservesCharge means that every matrix entry between unequal charges vanishes. Kills means that the matrix annihilates the basis ket and its dual row.")),
            Paragraph(Text("Hminus and Hplus sum the first and second densities printed in Eq. (46), respectively. The two agree with reversed coupling because the controlled square equals the control times the unextended square. Hladder sums the explicit plus-sign density in Eq. (71). The normalized right side of Eq. (57) uses the minus-sign base at cosine of mu, as fixed by Eq. (50).")),
            Paragraph(Text("The staggered correction uses the four cubic monomials, the two quadratic monomials and the ordered quartic monomial of Eq. (58) with their Eq. (59) coefficients. The ordered one-based pairs are (2,3), (4,5), through (L,1). Nonsingular means that the sines of v plus m and v minus m are both nonzero. The staggered conclusion uses even length and nonsingular parameters. The analytic identification with the derivative of Eq. (51) remains open and its regular domain also requires nonzero sine of mu.")),
            Describe.Lean(
                DescribeId.Create("miao-fukai-tiled-singletons"),
                DeclarationHandle.Create(Prefix + "tiled_singleton_components"),
                H("The common singleton family"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The embedding maps each Boolean block choice to the corresponding labelled tile word in its common charge sector. The image has exactly the displayed cardinality. The component supports are distinct singletons because the embedding is injective. Each basis ket is nonzero and has energy zero and projector charge equal to the sector label.")),
                    Paragraph(Text("Each local controlled generator has zero row and column on the tile words. Both controlled pieces of the linear and squared ladder terms vanish separately. Every ordered staggered monomial also vanishes because its rightmost factor kills the ket and its leftmost factor kills its dual. The charge-preserving entries make the fixed-charge graph the support graph of the actual sector restriction.")),
                    Paragraph(Text("This yields a lower bound on the number of singleton components in the specified native ladder sector. The four-representation expectation, the total component count and the largest-component asymptotics remain outside the theorem."))),
                DescribeRole.Theorem))));

    private static Formula Statement() =>
        All(L, Nat, All(HMin, Le(D(1, 2), L), new Formula.Aligned([
            And(Call("Odd", Seq(L, Minus, Call("targetCharge", L))),
                Eq(Call("card", Call("image", Call("sectorEmbedding", HMin))),
                    new Formula.Power(D(2), Call("blocks", L)))),
            Conjunct(All(Delta, Complex, And(Preserves(MinusHamiltonian()), Preserves(PlusHamiltonian()), Preserves(LadderHamiltonian())))),
            Conjunct(OnStaggeredDomain(Preserves(StaggeredHamiltonian()))),
            Conjunct(All(B, Seq(Call("Fin", Call("blocks", L)), To, Call("Bool")),
                Seq(Operatorname, Grp(F.Id("let")), Sp, Eq(X, Call("sectorEmbedding", HMin, B)), Comma, Sp,
                    And(Eq(Value(), Call("tiledConfig", HMin, B)),
                        Ne(Ket(), D(0)),
                        Eq(Call("mulVec", Call("NP", L), Ket()), Call("smul", Call("ofNat", Call("targetCharge", L)), Ket())),
                        Parens(All(Delta, Complex, And(Singleton(MinusHamiltonian()), Singleton(PlusHamiltonian()), Singleton(LadderHamiltonian())))),
                        Parens(OnStaggeredDomain(Singleton(StaggeredHamiltonian())))))))
        ])));

    private static Formula MinusHamiltonian() => Call("Hminus", L, Delta);
    private static Formula PlusHamiltonian() => Call("Hplus", L, Delta);
    private static Formula LadderHamiltonian() => Call("Hladder", L, Delta);
    private static Formula StaggeredHamiltonian() => Call("staggeredH", L, Mu, V);
    private static Formula Value() => Call("val", X);
    private static Formula Ket() => Call("ket", Value());
    private static Formula Preserves(Formula matrix) => Call("PreservesCharge", matrix);
    private static Formula OnStaggeredDomain(Formula body) =>
        Imp(Call("Even", L), All(Mu, Complex, All(V, Complex, Imp(Call("Nonsingular", Mu, V), body))));
    private static Formula Singleton(Formula matrix) =>
        And(Call("Kills", matrix, Value()),
            Eq(Call("componentSupport", Call("sectorSupport", matrix), X), Call("singleton", X)));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var symbol = Seq(Operatorname, Grp(F.Id(name)));
        return arguments.Length == 0 ? symbol : new Formula.Apply(symbol, [.. arguments]);
    }

    private static Formula Conjunct(Formula body) => Seq(Land, Sp, Parens(body));
    private static Formula Parens(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parens(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parens(a), FormulaLogicOperator.Implies, Parens(b));
    private static Formula And(Formula first, params Formula[] rest)
    {
        var result = first;
        foreach (var clause in rest)
            result = new Formula.Logic(result, FormulaLogicOperator.And, clause);
        return Parens(result);
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
