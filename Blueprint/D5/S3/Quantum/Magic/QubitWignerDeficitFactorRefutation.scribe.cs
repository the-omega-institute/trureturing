using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QubitWignerDeficitFactorRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/dutta2026wignerdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Wigner tensor deficit cannot factor as the equatorial state's Wigner distance times a function of the other state.",
        H("Failure of the factored Wigner deficit"),
        Blocks(
            Definition("deficit", "The tensor deficit", DeficitFormula(),
                "The deficit is (1+COne(rho))(1+COne(sigma))-1-CTwo(rho tensor sigma). The one-qubit and two-qubit distances use the Wootters frame and the convex hull of actual stabilizer Wigner vectors."),
            Definition("claim", "The factorization clause of Conjecture 5.5", Iff(V("claim"), ClaimFormula()),
                "Conjecture 5.5 asserts that the deficit factors as COne(rho) times a universal function of sigma whenever rho is equatorial magic and sigma has positive Bloch product. Equatorial magic means IsDensity(rho), bloch(rho,Z)=0, and COne(rho)>0. IsDensity means positive semidefinite with trace one. The additional conjectured conditions on the function, including nonnegativity and dependence on absolute Pauli coordinates, imply this factorization clause."),
            Describe.Lean(DescribeId.Create("dutta-factored-deficit-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The factored deficit is false"), StatementSource.FromAuthor(Disp(Seq(Neg, Sp, V("claim")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Take the pure Bloch vectors rhoA=(3/5,4/5,0), rhoB=(5/13,12/13,0), and sigma=(1/9,4/9,8/9). Their single-qubit distances are 1/5, 2/13, and 2/9. The joint distances are 7/18 and 79/234. A sign functional bounded by 1/2 on all sixty two-qubit stabilizer Wigner vectors proves the lower bounds, and five-stabilizer mixtures attain them. Four states in each mixture are Pauli spectral products, and the fifth is the common positive eigenstate of XY and YZ. Thus factorization would give both f(sigma)=7/18 and f(sigma)=17/36, which are unequal. Both equatorial states are pure, so the same contradiction holds if the equatorial input is restricted to pure states."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dutta-tushar-2026-wigner-distance-factored-deficit"), ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("dutta-factored-deficit-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula C(Formula rho) => Call("COne", rho);
    private static Formula Qubit() => V("QubitMatrix");
    private static Formula DeficitFormula()
    {
        var rho = V("rho"); var sigma = V("sigma");
        var joint = Call("CTwo", Call("kronecker", rho, sigma));
        return All("rho", Qubit(), All("sigma", Qubit(), Equal(Call("deficit", rho, sigma),
            Subtract(Subtract(Multiply(Parenthesized(Add(D(1), C(rho))),
                Parenthesized(Add(D(1), C(sigma)))), D(1)), joint))));
    }
    private static Formula ClaimFormula()
    {
        var rho = V("rho"); var sigma = V("sigma");
        var product = Multiply(Multiply(Call("bloch", sigma, V("X")), Call("bloch", sigma, V("Y"))), Call("bloch", sigma, V("Z")));
        return ExistsOne("f", new Formula.TypeArrow(Qubit(), Seq(Mathbb, Grp(V("R")))),
            All("rho", Qubit(), All("sigma", Qubit(), Imp(Call("IsDensity", rho),
                Imp(Equal(Call("bloch", rho, V("Z")), D(0)),
                    Imp(Rel(D(0), FormulaRelationOperator.LessThan, C(rho)),
                        Imp(Call("IsDensity", sigma), Imp(Rel(D(0), FormulaRelationOperator.LessThan, product),
                            Equal(Call("deficit", rho, sigma), Multiply(C(rho), Call("f", sigma)))))))))));
    }
}
