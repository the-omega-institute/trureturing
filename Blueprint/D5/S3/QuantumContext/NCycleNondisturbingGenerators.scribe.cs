using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class NCycleNondisturbingGeneratorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumContext/NCycleNondisturbingGenerators";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary nondisturbing cycle tables are convex combinations of deterministic and parity tables.",
        H("Generating binary nondisturbing cycle probabilities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-generators"),
                DeclarationHandle.Create(Module + ".allGenerators"),
                H("Deterministic and parity tables"),
                StatementSource.FromAuthor(Disp(AllGeneratorsFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each global assignment s, include the table concentrated on s(i) and "
                        + "s(finRotate n i) in context i. For each Boolean edge pattern γ, include "
                        + "the table with probability one half on each outcome pair satisfying "
                        + "b xor c = γ(i), and zero elsewhere. All edge patterns are included, "
                        + "without a parity restriction. This union is a generating set; the "
                        + "definition does not assert that every included table is an extreme point."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("decomposition"),
                DeclarationHandle.Create(Module + ".decomposition"),
                H("Every nondisturbing probability table is generated"),
                StatementSource.FromAuthor(Disp(DecompositionFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the directed graph with vertices (i,b) and edges (i,b,c) from (i,b) "
                            + "to (finRotate n i,c). Give each forward edge coefficient r(i,b,c)/n "
                            + "and each reverse edge coefficient zero. Nonnegativity of r gives "
                            + "nonnegative coefficients. Each layer has total mass one, so the "
                            + "sum of all coefficients is one. Nondisturbance says precisely that "
                            + "the incoming and outgoing masses agree at every vertex. These "
                            + "coefficients therefore form a normalized circulation.")),
                    Paragraph(Text(
                        "Decompose this circulation into a finite convex combination of normalized "
                            + "simple closed walks. For a positive-weight term, every reverse-edge "
                            + "multiplicity is zero by the positive_coefficient_forward theorem in LayeredFlow "
                            + "and the edge-multiplicity membership criterion: the original reverse "
                            + "coefficient is zero and every edge of a positive-weight circuit "
                            + "has forward orientation.")),
                    Paragraph(Text(
                        "A simple closed walk has at most one departure from each vertex. To see "
                            + "this, count departures by counting occurrences of the vertex along "
                            + "the walk, with the terminal occurrence removed, using the "
                            + "outgoingMultiplicity_edgeMultiplicity_concat theorem in SupplierGraph. "
                            + "The list before "
                            + "the terminal edge has no repeated vertex; a repetition would give "
                            + "a forbidden proper positive closed subwalk. Thus each row of the "
                            + "two-by-two edge-count table has sum at most one.")),
                    Paragraph(Text(
                        "For a walk with no reverse edges, balance at (finRotate n i,c) equates "
                            + "the incoming column sum from layer i to the outgoing row sum in "
                            + "the next layer. The total edge multiplicity per layer is consequently "
                            + "constant, say m, and the walk length is n m. The supplier theorem "
                            + "IsSimpleCycle.length_le_card bounds this length by 2n; together "
                            + "with positive length, this implies that m is either one or two.")),
                    Paragraph(Text(
                        "When m = 1, exactly one outcome s(i) has a departure in each layer. "
                            + "The next layer's row sums fix the current layer's column sums, so "
                            + "the unique edge in layer i joins s(i) to s(finRotate n i). Multiplying "
                            + "the normalized walk coefficients by n gives the deterministic "
                            + "table of s. When m = 2, both row sums and both column sums are "
                            + "one. Each layer's two-by-two count table is therefore one of the "
                            + "two permutation matrices. Set γ(i) according to whether its "
                            + "false-to-true edge has count one. After division by the walk "
                            + "length 2n and multiplication by n, its table has entries one half "
                            + "exactly when b xor c = γ(i). It is a parity table.")),
                    Paragraph(Text(
                        "Assign to each positive-weight walk the generating table just obtained. "
                            + "For a zero-weight walk use the deterministic table of the constant "
                            + "false assignment. Every chosen table belongs to allGenerators n. "
                            + "The original weights are nonnegative and sum to one. At each "
                            + "coordinate their weighted sum is n times the forward-edge "
                            + "coefficient r(i,b,c)/n, hence equals r(i,b,c). This gives the "
                            + "required membership in the real convex hull for every n > 0."))),
                DescribeRole.Theorem))));

    private static Formula AllGeneratorsFormula()
    {
        Formula deterministicCondition = And(Equal(At(X("s"), X("i")), X("b")),
            Equal(At(X("s"), Rotate(X("i"))), X("c")));
        Formula deterministicFamily = LambdaOf("s", Arrow(Fin(X("n")), BoolType()),
            LambdaOf("i", Fin(X("n")), LambdaOf("b", BoolType(), LambdaOf("c", BoolType(),
                At(Qualified("ite"), deterministicCondition, Real(1), Real(0))))));
        Formula parityCondition = Equal(At(Qualified("Bool", "xor"), X("b"), X("c")),
            At(X("γ"), X("i")));
        Formula parityFamily = LambdaOf("γ", Arrow(Fin(X("n")), BoolType()),
            LambdaOf("i", Fin(X("n")), LambdaOf("b", BoolType(), LambdaOf("c", BoolType(),
                At(Qualified("ite"), parityCondition, Divide(Real(1), Real(2)), Real(0))))));
        Formula union = At(Qualified("Set", "union"),
            At(Qualified("Set", "range"), deterministicFamily),
            At(Qualified("Set", "range"), parityFamily));
        return All("n", Naturals(), Equal(
            Typed(At(Local("allGenerators"), X("n")), At(Qualified("Set"), Table())), union));
    }

    private static Formula DecompositionFormula()
    {
        Formula positive = All("i", Fin(X("n")), All("b", BoolType(), All("c", BoolType(),
            LE(Real(0), At(X("r"), X("i"), X("b"), X("c"))))));
        Formula normalized = All("i", Fin(X("n")), Equal(
            SumOf("b", SumOf("c", At(X("r"), X("i"), X("b"), X("c")))), Real(1)));
        Formula consistent = All("i", Fin(X("n")), All("c", BoolType(), Equal(
            SumOf("b", At(X("r"), X("i"), X("b"), X("c"))),
            SumOf("d", At(X("r"), Rotate(X("i")), X("c"), X("d"))))));
        Formula conclusion = Member(X("r"), At(Qualified("convexHull"), Reals(),
            At(Local("allGenerators"), X("n"))));
        return All("n", Naturals(), Imp(LT(Typed(D(0), Naturals()), X("n")),
            All("r", Table(), Imp(positive, Imp(normalized, Imp(consistent, conclusion))))));
    }

    private static Formula X(string name) => name == "γ" ? GammaLower : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "QuantumContext",
        "NCycleNondisturbingGenerators", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Real(byte value) => Typed(D(value), Reals());
    private static Formula BoolType() => Qualified("Bool");
    private static Formula Fin(Formula n) => At(Qualified("Fin"), n);
    private static Formula Table() => Arrow(Fin(X("n")), Arrow(BoolType(), Arrow(BoolType(), Reals())));
    private static Formula Rotate(Formula i) => At(At(Qualified("Equiv", "toFun"),
        At(Qualified("finRotate"), X("n"))), i);
    private static Formula SumOf(string name, Formula body) => At(Qualified("Finset", "sum"),
        Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), BoolType())),
        LambdaOf(name, BoolType(), body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Divide(Formula left, Formula right) =>
        new Formula.Fraction(Parenthesized(left), Parenthesized(right));
}
