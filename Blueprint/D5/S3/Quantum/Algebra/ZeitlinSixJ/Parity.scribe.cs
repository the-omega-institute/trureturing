using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class ParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/Parity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J Parity"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("physical_signed_addition", "physical signed addition", F0(),
                "The parity-twisted physical Racah matrix equals the second normalized Racah matrix. Its Jacobi equation, symmetry and signed endpoint entry identify it uniquely.", DescribeRole.Lemma, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-parity-" + name.Replace("_", "-").Replace(".", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(N("l"),
        FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Call("physicalX", N("n"), N("j"), N("l")),
        FormulaRelationOperator.Equal, Call("physicalZ", N("n"), N("j"), N("l")))))))))))));
}
