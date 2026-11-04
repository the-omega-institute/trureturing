using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OrderedGNSProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful matrix states detect positivity through internal compressions of a star-subalgebra.",
        H("Ordered GNS Projections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("internal-compressions-detect-positivity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/OrderedGNSProjection.positive_of_internal_compressions"),
                H("Internal compressions detect positivity"),
                StatementSource.FromAuthor(InternalPositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an arbitrary positive definite complex matrix rho and a unital star-subalgebra A. "
                        + "A Hermitian matrix y in A is positive semidefinite if every compression q-star y q, "
                        + "with q in A, has nonnegative real rho-weighted trace.")),
                    Paragraph(Text(
                        "Continuous functional calculus keeps the square root of the negative part of y in A. "
                        + "Its compression is the negative of the square of that negative part. "
                        + "Faithfulness of the weighted matrix inner product forces the negative part to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-gns-characterization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/OrderedGNSProjection.ordered_gns_characterization"),
                H("Ordered comparisons and complete positivity"),
                StatementSource.FromAuthor(CharacterizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be any positive definite complex matrix of trace one, and let A be any "
                        + "unital star-subalgebra on the same finite carrier. The map E is the unique "
                        + "orthogonal projection onto A for the inner product tr(rho x-star y). "
                        + "Its left ordered comparisons determine E without any positivity assumption.")),
                    Paragraph(Text(
                        "Retraction, preservation of the unit and state, and the left module law follow "
                        + "from that orthogonal projection. The additional complex identity "
                        + "tr(rho E(x) a) = tr(rho x a), for every a in A, holds exactly when E preserves "
                        + "adjoints. Conjugating the left module law then gives the right module law.")),
                    Paragraph(Text(
                        "For a positive input, bimodularity and state preservation make all internal "
                        + "compressions of its image nonnegative under the faithful state. The preceding "
                        + "positivity test therefore makes the image positive. At every finite matrix "
                        + "amplification the block algebra M_k(A), the entrywise map id tensor E, and the "
                        + "faithful density I_k tensor rho satisfy the same identities. This density "
                        + "evaluates a matrix as the sum of its diagonal-block states; for nonzero k, "
                        + "division by k gives the normalized amplified state and preserves the sign test. "
                        + "The empty amplification is included. Thus every actual PSD input has a PSD image.")),
                    Paragraph(Text(
                        "The resulting expectation is unital, completely positive, idempotent, state "
                        + "preserving and an A-bimodule map, with image exactly A. Conversely, its bimodule "
                        + "and state identities recover the original right ordered comparison. The "
                        + "equivalence concerns these three conditions; no modular-flow or block "
                        + "classification is asserted.")),
                    Paragraph(Text(
                        "In the display, M is the full complex matrix algebra on n, state(rho,x) is "
                        + "tr(rho*x), and E is defined to be projection(rho,hrho,A), the actual weighted "
                        + "orthogonal projection. The final parenthesized condition expands exactly "
                        + "Expectation(rho,A,E). IsPositive, IsCompletelyPositive and kron are the "
                        + "PhyslibLeaf.MatrixMap predicates and tensor map. The identity in Ek is the "
                        + "complex-linear identity on matrices indexed by Fin k. The density "
                        + "amplifiedDensity(Fin k,rho) is k-inverse times (I_k tensor rho), using the "
                        + "real scalar inverse, including k=0. Every matrix variable and both ordered "
                        + "comparisons retain their full complex values."))),
                DescribeRole.Theorem))));

    private static Formula StarOf(Formula value) => Seq(value, Caret, Grp(Star));
    private static Formula StateOf(Formula rho, Formula value) => Call("state", rho, value);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Par(body));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Iff, Par(right));
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Mem(Formula value, Formula algebra) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, algebra);
    private static Formula Apply(Formula map, Formula value) => new Formula.Apply(map, [value]);
    private static Formula Typed(Formula value, Formula type) => Par(Seq(value, Colon, Sp, type));
    private static Formula Let(string name, Formula type, Formula value, Formula body) => Seq(
        Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Colon, Sp, type,
        Sp, Colon, Eq, Sp, value, Semi, Sp, Par(body));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula MatrixOn(Formula carrier) => Call("Matrix", carrier, carrier, Complexes());
    private static Formula LinearEnd(Formula space) => Call("LinearMap", Complexes(), space, space);

    private static Formula MatrixContext(Formula body, bool normalized)
    {
        Formula n = F.Id("n");
        Formula rho = F.Id("rho");
        Formula matrix = F.Id("M");
        Formula algebras = All("A", Call("StarSubalgebra", Complexes(), matrix), body);
        Formula traceContext = normalized
            ? All("htrace", Eqn(Call("trace", rho), D(1)), algebras)
            : algebras;
        return All("n", Seq(F.Id("Type"), Star), Seq(
            OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", n), CloseBracket, Comma, Sp,
            Let("M", Seq(F.Id("Type"), Star), MatrixOn(n),
                All("rho", matrix, All("hrho", Call("PosDef", rho), traceContext)))));
    }

    private static Formula InternalPositivityFormula()
    {
        Formula rho = F.Id("rho");
        Formula matrix = F.Id("M");
        Formula y = F.Id("y");
        Formula q = F.Id("q");
        Formula algebra = F.Id("A");
        Formula test = All("q", matrix, Imp(Mem(q, algebra),
            Seq(D(0), Leq, Re, StateOf(rho, Seq(StarOf(q), y, q)))));
        return Disp(MatrixContext(All("y", matrix,
            Imp(Call("IsHermitian", y), Imp(Mem(y, algebra),
                Imp(test, Call("PosSemidef", y))))), normalized: false));
    }

    private static Formula CharacterizationFormula()
    {
        Formula rho = F.Id("rho");
        Formula matrix = F.Id("M");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula a = F.Id("a");
        Formula e = F.Id("E");
        Formula algebra = F.Id("A");
        Formula Ex = Apply(e, x);
        Formula comparison(Formula value) => Eqn(
            StateOf(rho, Seq(StarOf(a), value)), StateOf(rho, Seq(StarOf(a), x)));
        Formula right = All("x", matrix, All("a", matrix, Imp(Mem(a, algebra),
            Eqn(StateOf(rho, Seq(Ex, a)), StateOf(rho, Seq(x, a))))));
        Formula membership = All("x", matrix, Mem(Ex, algebra));
        Formula left = All("x", matrix, All("a", matrix,
            Imp(Mem(a, algebra), comparison(Ex))));
        Formula unique = All("x", matrix, All("y", matrix, Imp(Mem(y, algebra),
            Imp(All("a", matrix, Imp(Mem(a, algebra), comparison(y))), Eqn(y, Ex)))));
        Formula adjoint = All("x", matrix, Eqn(Apply(e, StarOf(x)), StarOf(Ex)));
        Formula conclusion = And(Eqn(StateOf(rho, D(1)), D(1)),
            And(membership, And(left, And(unique,
                And(IffOf(right, adjoint), IffOf(right, ExpectationFormula()))))));
        return Disp(MatrixContext(
            Let("E", LinearEnd(matrix), Call("projection", rho, F.Id("hrho"), algebra), conclusion),
            normalized: true));
    }

    private static Formula ExpectationFormula()
    {
        Formula rho = F.Id("rho");
        Formula matrix = F.Id("M");
        Formula algebra = F.Id("A");
        Formula e = F.Id("E");
        Formula x = F.Id("x");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula k = F.Id("k");
        Formula ek = F.Id("Ek");
        Formula bigX = F.Id("X");
        Formula indices = Call("Fin", k);
        Formula blocks = MatrixOn(indices);
        Formula amplified = MatrixOn(Par(Seq(indices, Sp, Times, Sp, F.Id("n"))));
        Formula density = Call("amplifiedDensity", indices, rho);
        Formula Ex = Apply(e, x);
        Formula finiteAmplifications = All("k", Seq(Mathbb, Grp(F.Id("N"))),
            Let("Ek", LinearEnd(amplified),
                Call("kron", Typed(F.Id("id"), LinearEnd(blocks)), e),
                And(Call("IsPositive", ek), And(Eqn(Apply(ek, D(1)), D(1)),
                    All("X", amplified, Eqn(StateOf(density, Apply(ek, bigX)),
                        StateOf(density, bigX)))))));
        Formula bimodule = All("a", matrix, Imp(Mem(a, algebra),
            All("b", matrix, Imp(Mem(b, algebra), All("x", matrix,
                Eqn(Apply(e, Seq(a, x, b)), Seq(a, Ex, b)))))));
        return And(Eqn(Apply(e, D(1)), D(1)),
            And(Call("IsCompletelyPositive", e),
                And(And(Call("IsPositive", e), finiteAmplifications),
                    And(All("x", matrix, Eqn(Apply(e, Ex), Ex)),
                        And(Eqn(Call("range", e), Call("carrier", algebra)),
                            And(All("x", matrix, Eqn(StateOf(rho, Ex), StateOf(rho, x))),
                                bimodule))))));
    }
}
