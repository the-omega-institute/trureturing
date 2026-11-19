using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Comparison;

internal sealed class TwoReadoutNormalizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affine equation for two translates of a bounded group function determines a common offset.",
        H("Affine Two-Readout Normalization"),
        Blocks(
            Describe.Lean(DescribeId.Create("two-readout-coefficient"),
                DeclarationHandle.Create(Module + ".coefficient_eq_neg_one"),
                H("The coefficient at a non-involutive step"),
                StatementSource.FromAuthor(CoefficientStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating the one-sided law at the step and its inverse gives two equations. "
                    + "Their difference shows that one plus the forward coefficient annihilates "
                    + "the difference between the readout at the square and the identity. "
                    + "Faithfulness makes that difference nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-dalembert-normalization"),
                DeclarationHandle.Create(Module + ".bounded_dalembert_of_affine_law"),
                H("Normalization of the symmetric affine law"),
                StatementSource.FromAuthor(SymmetricStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The group is arbitrary. Centrality and invariance under inversion let the "
                    + "two arguments of the symmetric readout exchange roles. Evaluation at "
                    + "the identity then ties the two coefficient functions to one common "
                    + "offset. If the linear coefficient were always two, the defect from one "
                    + "would grow under squaring, contradicting boundedness. The normalized "
                    + "equation gives duplication, which both forces the offset below one and "
                    + "bounds the normalized function between minus one and one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("one-sided-dalembert-normalization"),
                DeclarationHandle.Create(Module + ".bounded_dalembert_of_one_sided_law"),
                H("The one-sided law when only the identity squares to the identity"),
                StatementSource.FromAuthor(OneSidedStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every nonidentity step, faithfulness forces the forward coefficient "
                    + "to be minus one. The identity step already has a symmetric law with "
                    + "linear coefficient two and offset zero. The symmetric normalization "
                    + "therefore applies to the entire group."))),
                DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula G => F.Id("G");
    private static Formula FunType => F.Seq(G, F.Sp, F.To, F.Sp, R);
    private static Formula P => F.Id("p");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula D => F.Id("d");
    private static Formula U => F.Id("u");
    private static Formula Z => F.Id("z");
    private static Formula X => F.Id("g");
    private static Formula Hh => F.Id("h");
    private static Formula M => F.Id("m");
    private static Formula One => F.D(1);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.BindMany(quantifier, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Read(Formula x) => App(P, x);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Ne(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.NotEqual, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Lt(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThan, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula If(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Iff(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Iff, r);
    private static Formula Mul(Formula l, Formula r) => F.Seq(l, F.Sp, F.Cdot, F.Sp, r);
    private static Formula Add(Formula l, Formula r) => F.Seq(l, F.Sp, F.Plus, F.Sp, r);
    private static Formula Sub(Formula l, Formula r) => F.Seq(l, F.Sp, F.Minus, F.Sp, r);
    private static Formula Inv(Formula x) => new Formula.Power(x, new Formula.Negate(One));
    private static Formula Even => All("g", G, Eq(Read(Inv(X)), Read(X)));
    private static Formula Central => All("g", G, All("h", G, Eq(Read(Mul(Mul(Hh, X), Inv(Hh))), Read(X))));
    private static Formula Faithful => All("g", G, Iff(Eq(Read(X), One), Eq(X, One)));
    private static Formula Bound => All("g", G, Le(new Formula.Absolute(Read(X)), One));
    private static Formula Nonconstant => Ex("g", G, Ne(Read(X), One));
    private static Formula OneSidedLaw => All("z", G, Eq(Read(Mul(Z, Inv(U))),
        Add(Add(Mul(A, Read(Z)), Mul(B, Read(Mul(Z, U)))), D)));
    private static Formula SymmetricLaw => All("z", G, All("u", G,
        Eq(Add(Read(Mul(Z, U)), Read(Mul(Z, Inv(U)))), Add(Mul(App(A, U), Read(Z)), App(D, U)))));
    private static Formula Offset(Formula x) => new Formula.Fraction(Sub(Read(x), M), Sub(One, M));

    private static Formula Normalized()
    {
        Formula bound = All("g", G, Le(new Formula.Absolute(Offset(X)), One));
        Formula equation = All("z", G, All("u", G, Eq(Add(Offset(Mul(Z, U)), Offset(Mul(Z, Inv(U)))),
            Mul(Mul(F.D(2), Offset(Z)), Offset(U)))));
        return Ex("m", R, And(Lt(M, One), And(bound, equation)));
    }

    private static Formula CoefficientStatement() => F.Disp(All("p", FunType,
        If(Even, If(Central, If(Faithful,
            All("a", R, All("b", R, All("d", R, All("u", G,
                If(OneSidedLaw, If(Ne(Mul(U, U), One), Eq(B, new Formula.Negate(One)))))))))))));

    private static Formula SymmetricStatement() => F.Disp(All("p", FunType,
        If(Eq(Read(One), One), If(Even, If(Central, If(Bound, If(Nonconstant,
            All("a", FunType, All("d", FunType, If(SymmetricLaw, Normalized()))))))))));

    private static Formula OneSidedStatement()
    {
        Formula involutions = All("u", G, If(Eq(Mul(U, U), One), Eq(U, One)));
        Formula laws = All("u", G, If(Ne(U, One), Ex("a", R, Ex("b", R, Ex("d", R, OneSidedLaw)))));
        return F.Disp(All("p", FunType, If(Even, If(Central, If(Faithful,
            If(Bound, If(Nonconstant, If(involutions, If(laws, Normalized())))))))));
    }
}
