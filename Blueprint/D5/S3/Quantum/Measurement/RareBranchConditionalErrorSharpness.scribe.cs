using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class RareBranchConditionalErrorSharpnessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/RareBranchConditionalErrorSharpness."
            + "rare_branch_conditional_error_sharpness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrarily small initial state error can reach maximal error after conditioning on a rare branch.",
        H("Rare-Branch Conditional Error Sharpness"),
        Blocks(Describe.Lean(
            DescribeId.Create("rare-branch-conditional-error-sharpness"),
            DeclarationHandle.Create(Declaration),
            H("A rare branch reaches maximal conditional error"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every positive epsilon below one, the displayed diagonal density states "
                        + "have trace distance epsilon while the same single-Kraus branch has "
                        + "equal probability epsilon on both states.")),
                Paragraph(Text(
                    "After normalization, the two branch outputs are orthogonal rank-one "
                        + "projectors, so their trace distance is one and the weighted sharpness "
                        + "identity is attained.")),
                Paragraph(Text(
                    "The construction also rules out any uniform conditional-error bound whose "
                        + "value tends to zero with the initial trace distance."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Open, source, Close, Sp, To, Sp, target);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Not(Formula value) => new Formula.Not(value);

    private static Formula ForAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula MatrixType(Formula index, Formula scalar) =>
        Call("Matrix", index, index, scalar);

    private static Formula Adj(Formula value) => Seq(Grp(value), Caret, Grp(Star));

    private static Formula Product(params Formula[] factors)
    {
        Formula result = factors[0];
        for (var index = 1; index < factors.Length; index++)
            result = Seq(result, Sp, Cdot, Sp, factors[index]);
        return result;
    }

    private static Formula Difference(Formula left, Formula right) =>
        Seq(Open, left, Sp, Minus, Sp, right, Close);

    private static Formula TheoremFormula()
    {
        Formula epsilon = F.Id("epsilon"), rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula pm = F.Id("P"), k = F.Id("K"), f = F.Id("f"), p = F.Id("p"), q = F.Id("q");
        Formula fin3 = Call("Fin", D(3));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = MatrixType(fin3, complex);
        Formula density = Call("DensityState", fin3);
        Formula c = Call("diag", D(1), D(0), D(0));
        Formula e0 = Call("diag", D(0), D(1), D(0));
        Formula e1 = Call("diag", D(0), D(0), D(1));
        Formula rhoM = Call("diag", Seq(D(1), Minus, epsilon), epsilon, D(0));
        Formula sigmaM = Call("diag", Seq(D(1), Minus, epsilon), D(0), epsilon);
        Formula branch = Seq(e0, Sp, Plus, Sp, e1);
        Formula traceDistance = Call("traceDistance", rho, sigma);
        Formula cond(Formula state, Formula probability, Formula projector) =>
            Eq(Seq(D(1), Sp, Slash, Sp, probability, Sp, Cdot, Sp,
                Product(pm, state, Adj(pm))), projector);
        Formula normalizedRho = Product(
            Seq(D(1), Sp, Slash, Sp, epsilon), Product(pm, Call("matrix", rho), Adj(pm)));
        Formula normalizedSigma = Product(
            Seq(D(1), Sp, Slash, Sp, epsilon), Product(pm, Call("matrix", sigma), Adj(pm)));
        Formula matrixDistance = Seq(
            Call("traceNorm", Difference(normalizedRho, normalizedSigma)),
            Sp, Slash, Sp, D(2));
        Formula weightedDistance = Product(Call("max", epsilon, epsilon), matrixDistance);
        Formula instrumentIdentity = Eq(
            Seq(Product(Adj(pm), pm), Sp, Plus, Sp, Product(Adj(k), k)), D(1));
        Formula witnessConjunction = And(
                            Eq(Call("matrix", rho), rhoM),
                            Eq(Call("matrix", sigma), sigmaM),
                            Eq(pm, branch), Eq(k, c),
                            instrumentIdentity,
                            Le(Product(Adj(pm), pm), D(1)),
                            Eq(traceDistance, epsilon),
                            Eq(Call("ReTr", Product(Call("matrix", rho), Product(Adj(pm), pm))), epsilon),
                            Eq(Call("ReTr", Product(Call("matrix", sigma), Product(Adj(pm), pm))), epsilon),
                            cond(Call("matrix", rho), epsilon, e0),
                            cond(Call("matrix", sigma), epsilon, e1),
                            Eq(Seq(Call("traceNorm", Difference(e0, e1)), Sp, Slash, Sp, D(2)), D(1)),
                            Eq(pm, branch),
                            Eq(weightedDistance, traceDistance));
        Formula firstWitness = Exists("rho", density,
            Exists("sigma", density,
                Exists("P", matrix,
                    Exists("K", matrix, witnessConjunction))));
        Formula first = ForAll("epsilon", real,
            Imp(And(Lt(D(0), epsilon), Lt(epsilon, D(1))), firstWitness));
        Formula positive = And(
            Lt(D(0), Call("ReTr", Product(Call("matrix", rho), Product(Adj(pm), pm)))),
            Lt(D(0), Call("ReTr", Product(Call("matrix", sigma), Product(Adj(pm), pm)))));
        Formula denominatorRho = Call("ReTr",
            Product(Call("matrix", rho), Product(Adj(pm), pm)));
        Formula denominatorSigma = Call("ReTr",
            Product(Call("matrix", sigma), Product(Adj(pm), pm)));
        Formula boundRho = Product(
            Seq(D(1), Sp, Slash, Sp, denominatorRho),
            Product(pm, Call("matrix", rho), Adj(pm)));
        Formula boundSigma = Product(
            Seq(D(1), Sp, Slash, Sp, denominatorSigma),
            Product(pm, Call("matrix", sigma), Adj(pm)));
        Formula bound = Le(
            Seq(Call("traceNorm", Difference(boundRho, boundSigma)),
                Sp, Slash, Sp, D(2)),
            Call("f", traceDistance));
        Formula pointwise = Imp(And(Le(Product(Adj(pm), pm), D(1)), positive), bound);
        Formula allP = ForAll("P", matrix, pointwise);
        Formula allSigma = ForAll("sigma", density, allP);
        Formula allRho = ForAll("rho", density, allSigma);
        Formula universal = And(
            Call("Tendsto", f, Call("nhdsGT", D(0)), Call("nhds", D(0))),
            allRho);
        Formula noUniform = Not(Exists("f", Arrow(real, real), universal));
        return Disp(And(first, noUniform));
    }
}
