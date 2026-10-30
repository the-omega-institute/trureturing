using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ConstraintRelations;

internal sealed class RationalZeroRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonnegative rational Boolean probability law is an exact finite five-mode marginal.",
        H("Exact rational five-mode networks with internal zeros"),
        Blocks(
            Node("rational-triples", "Ordered Boolean triples", "Triple", StatementSource.WithoutFormula(),
                "A triple is an ordered element of Bool times Bool times Bool. The two Boolean values are written zero and one.", DescribeRole.Definition),
            Node("rational-tables", "Legal full probability tables", "Table", StatementSource.WithoutFormula(),
                "A table assigns a nonnegative rational to each of the eight ordered Boolean triples. Its eight entries sum to one. It vanishes outside the existing relation A, consisting of 000, 100, 010, 110 and 001. Extra zeros within A are allowed; these are the W0 tables. Normalization concerns the full table even when a repeated scope visits fewer entries.", DescribeRole.Definition),
            Node("rational-factors", "Scopes on actual variables", "Factor", StatementSource.WithoutFormula(),
                "A factor on a variable type V consists of an ordered triple of members of V and a legal Table. Scope entries may repeat. There are no scope constructors for constants or complemented literals, and no extra equality, unary or multivariate primitive.", DescribeRole.Definition),
            Node("rational-factor-value", "Evaluating a factor", "value", StatementSource.WithoutFormula(),
                "Given a Boolean assignment to V, evaluate its three actual scope variables in order and read that tuple's table entry.", DescribeRole.Definition),
            Node("rational-network", "Finite visible and hidden counts", "Network", StatementSource.WithoutFormula(),
                "For natural n, m and k, a network consists of k factors whose variable names belong to the disjoint union Fin n plus Fin m. The first summand names the n visible variables; the second names the m hidden variables. Both m and k are arbitrary finite counts.", DescribeRole.Definition),
            Node("rational-weight", "The full assignment weight", "weight", StatementSource.WithoutFormula(),
                "The weight at visible assignment a and hidden assignment h is the finite product over all factors, each evaluated in the combined assignment Sum.elim a h. An empty product is one.", DescribeRole.Definition),
            Node("rational-marginal", "Summing every hidden assignment", "marginal", StatementSource.WithoutFormula(),
                "The marginal at a sums the full assignment weight over every function from Fin m to Bool. No consistency predicate restricts this summation domain.", DescribeRole.Definition),
            Node("rational-partition", "The partition function", "partition", StatementSource.WithoutFormula(),
                "The partition function sums the marginal over every visible assignment. Equivalently it sums the weight over all visible and hidden assignments.", DescribeRole.Definition),
            Node("rational-law", "Final normalization", "law", StatementSource.WithoutFormula(),
                "The law at a is the marginal at a divided by the partition function. The representation theorem proves that the partition function is strictly positive.", DescribeRole.Definition),
            Node("rational-pin-raw", "The indicator potential", "pinRaw", StatementSource.WithoutFormula(),
                "The raw pin potential is one on each of the five tuples of A and zero on the remaining three tuples.", DescribeRole.Definition),
            Node("rational-pin-table", "The normalized exclusion table", "pinTable", StatementSource.WithoutFormula(),
                "Divide the raw pin potential by five. On (o,o,o) this forces the actual variable o to zero. On (u,u,w) it enforces that u and w are not simultaneously one, including a loop when u=w.", DescribeRole.Definition),
            Node("rational-unary-raw", "The full activity potential", "unaryRaw", StatementSource.WithoutFormula(),
                "For rational r, the raw activity potential has value r at 110, value one at the four other tuples of A, and zero outside A. All eight entries are specified.", DescribeRole.Definition),
            Node("rational-unary-table", "The normalized activity table", "unaryTable", StatementSource.WithoutFormula(),
                "For r nonnegative, divide the raw activity potential by four plus r. With an internally zero pin o, scope (u,u,o) has activities one and r, times the common normalization factor. When r is positive, every tuple of A has positive value.", DescribeRole.Definition),
            Node("rational-numbering", "Numbering finite hidden and factor types", "numberedNetwork", StatementSource.WithoutFormula(),
                "Given finite types H and J, a decidable equality on H and a family f indexed by J of actual factors on Fin n plus H, finite equivalences produce a Network n card(H) card(J). Visible names stay fixed. Hidden names and factor indices are renamed bijectively. Every Table is retained without alteration.", DescribeRole.Definition),
            Node("rational-numbered-marginal", "Marginals are unchanged by finite numbering", "numbered_marginal", StatementSource.FromAuthor(NumberedFormula()),
                "For every natural n, finite types H and J, a decidable equality on H, every factor family f on Fin n plus H and every visible assignment a, the canonical numbered Network marginal equals the sum over all h from H to Bool of the product over all j in J of the actual factor values in combined(a,h), the assignment Sum.elim a h. Empty types and empty products are included.", DescribeRole.Theorem),
            Node("rational-zero-realization", "Every rational law, including arbitrary zeros", "result", StatementSource.FromAuthor(ResultFormula()),
                "Let n be any natural number at least one. Let P be any rational function on the entire n-dimensional Boolean cube with nonnegative entries summing to one. There exist finite natural m and k and a Network n m k whose partition function is positive and whose normalized marginal equals P at every visible assignment. Arbitrary zero entries are included. No bound on the finite network size is asserted.", DescribeRole.Theorem),
            Paragraph(Text("For each visible word s, build a NOR expression testing equality with s. A positive target bit uses the visible input; a negative target bit uses NOR of that input with itself. Conjunction is NOR of the two NOR-computed negations. A fold joins all n literals, seeded by the first literal; duplicating that literal preserves the indicator and requires no constant. The finite union of the expressions' gate subterms gives hidden wires. A shared subexpression denotes one actual wire. Structural induction proves that gate equations determine every hidden gate wire uniquely for each visible assignment.")),
            Paragraph(Text("The NOR factor is the indicator of the existing null-deleted relation N divided by four. Its four allowed triples are 100, 010, 110 and 001, so every gate factor is a legal W0 table. A fresh hidden wire o has the table indicator of A divided by five on scope (o,o,o). This internally forces o to zero. It supplies no external constant.")),
            Paragraph(Text("For each s, use the full table U with entries one at 000, 100, 010 and 001, entry P(s) at 110, and zero outside A. Its positive table sum is four plus P(s), including when P(s) is zero. Divide by that sum and attach it to (e_s,e_s,o), where e_s is the actual wire computing the equality indicator. Thus the apparent unary weight is implemented by an allowed ordered ternary factor.")),
            Paragraph(Text("Exactly one indicator is true at a, namely the one indexed by a. The unique gate-consistent hidden assignment therefore has weight C times P(a), where C is one fifth times one fourth for each gate times the product over s of one divided by the quantity four plus P(s). Every factor of C is positive rational. Every other hidden assignment violates the pin or a gate and contributes zero. The hidden marginal is exactly C times P(a); its total is C because P sums to one. Final normalization gives P exactly, with no limit. Finite equivalences number the hidden and factor sets without changing any sums or products.")),
            Paragraph(Text("This is an elementary constructive consequence of the five-mode relation and NOR computation. It concerns globally normalized potentials, not a supplied causal sampling kernel or an efficiency bound. The existing unweighted primitive-positive support theorem alone does not specify the rational masses."))
        ), []));

    private static Formula NumberedFormula()
    {
        Formula n = F.Id("n"), hType = F.Id("H"), jType = F.Id("J"), f = F.Id("f"), a = F.Id("a"), h = F.Id("h"), j = F.Id("j");
        Formula cube = Arrow(Call("Fin", n), Named("Bool"));
        Formula variables = Seq(Call("Fin", n), Sp, F.Plus, Sp, hType);
        Formula value = Call("value", Call("f", j), Call("combined", a, h));
        Formula product = Seq(F.Prod, Underscore, Grp(j, Sp, InMacro, Sp, jType), Sp, value);
        Formula sum = Seq(F.Sum, Underscore, Grp(h, Sp, InMacro, Sp, Arrow(hType, Named("Bool"))), Sp, product);
        Formula statement = All("a", cube,
            Rel(Call("marginal", Call("numberedNetwork", f), a), FormulaRelationOperator.Equal, sum));
        statement = All("f", Arrow(jType, Call("Factor", variables)), statement);
        statement = Seq(OpenBracket, Call("Fintype", hType), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", hType), CloseBracket, Sp,
            OpenBracket, Call("Fintype", jType), CloseBracket, Sp, statement);
        statement = All("J", Named("Type"), statement);
        statement = All("H", Named("Type"), statement);
        return Disp(All("n", Named("Nat"), statement));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), k = F.Id("k"), a = F.Id("a"), net = F.Id("net");
        Formula nat = Named("Nat"), rat = Named("Rat"), cube = Arrow(Call("Fin", n), Named("Bool"));
        Formula hypotheses = And(All("a", cube, Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Call("P", a))),
            Rel(Seq(F.Sum, Underscore, Grp(a, Sp, InMacro, Sp, cube), Sp, Call("P", a)), FormulaRelationOperator.Equal, D(1)));
        Formula conclusion = Exists("m", nat, Exists("k", nat, Exists("net", Call("Network", n, m, k),
            And(Rel(D(0), FormulaRelationOperator.LessThan, Call("partition", net)),
                All("a", cube, Rel(Call("law", net, a), FormulaRelationOperator.Equal, Call("P", a)))))));
        return Disp(All("n", nat, Imp(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, n),
            All("P", Arrow(cube, rat), Imp(hypotheses, conclusion)))));
    }

    private static DocumentBlock Node(string id, string title, string name, StatementSource statement,
        string prose, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Close, Sp, To, Sp, b);
    private static Formula All(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Exists(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
}
