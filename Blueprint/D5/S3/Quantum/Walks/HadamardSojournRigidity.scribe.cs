using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Walks;

internal sealed class HadamardSojournRigidityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Walks/HadamardSojournRigidity";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/tamurayamagami2026sojourn");

    private static readonly Formula U = Id("U");
    private static readonly Formula N = Seq(Mathbb, Grp(Id("N")));
    private static readonly Formula C = Seq(Mathbb, Grp(Id("C")));
    private static readonly Formula FinTwo = Call("Fin", Num(2));
    private static readonly Formula Coin = Call("Matrix", FinTwo, FinTwo, C);
    private static readonly Formula Vector = Seq(FinTwo, Sp, To, Sp, C);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Time-eight and time-4m rigidity for every two-state unitary coin and every unit initial state in the fixed direction basis.",
        H("Hadamard rigidity of positive sojourn time"),
        Blocks(
            Entry("amplitude", "Coherent return amplitude", AmplitudeFormula(),
                "The direction labels zero and one select the left and right rows of the coin. "
                    + "Generate each word of length n once. Keep the words whose displacement is zero "
                    + "and whose positive interval count is k. An interval contributes if its start is positive "
                    + "or its start is zero and the next step is right. Multiply the projected coins with later "
                    + "steps on the left and add the matrices over the retained words. The empty word has "
                    + "the identity matrix. These are the conventions in Section 2, printed pages 3 and 4.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("weight", "Unnormalized weight", WeightFormula(),
                "Apply the coherent return amplitude to the initial coin vector and sum the squared moduli "
                    + "of its two output coordinates. This is the weight defined in Section 2, printed page 4.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("exactUniform", "Exact conditional uniformity", UniformFormula(),
                "The denominator T sums the weights at time 4m over the counts zero through 4m. "
                    + "Exact uniformity requires T to be positive. For positive m it assigns mass 1/(2m−1) "
                    + "to each even count strictly between zero and 4m and zero to every other natural count. "
                    + "The subtraction in the denominator is in the real numbers. "
                    + "Definition 3.1 gives the support and the common mass for positive m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("exactUniform_rigidity", "The time-eight test and uniformity at every positive multiple of four", RigidityFormula(),
                "Here H denotes conjugate transpose and 1 is the identity matrix in the unitarity equation. "
                    + "In the fixed direction basis, U factors as D R E with diagonal unitaries D and E "
                    + "and R having rows (c,s) and (s,−c), where c and s are nonnegative. "
                    + "A return word takes equally many left and right steps. Its projected product therefore "
                    + "has a common phase depending only on its length and transforms by multiplication "
                    + "by the adjoint of E on the left and by E on the right. "
                    + "The conditional law for U on the initial vector equals the law for R on that vector "
                    + "multiplied by E. For R, the sum of the Gram matrices at counts two and six minus "
                    + "twice the Gram matrix at count four is 2c⁴s⁶(c²−s²)²(c²+s²) times the identity. "
                    + "The weight at count four must be positive, which excludes either parameter being zero. "
                    + "Equality of the three weights then forces c = s. For the balanced coin, the path "
                    + "recurrence has a solution in formal series whose coefficients are polynomials in the "
                    + "sojourn marker. On each half-line the solution is a power of a two-by-two transfer "
                    + "matrix. The transfer matrices satisfy the first-return recurrence with the Catalan series. "
                    + "The equation at the origin determines the return series. Rescaling time by the imaginary "
                    + "unit and adding gives the even-in-semilength projection. At time 4m the resulting "
                    + "sojourn polynomial is the sum of the powers with exponents 2,4,…,4m−2 times "
                    + "the matrix with rows (1,1) and (−1,1), scaled by (−1)ᵐ Cat(m−1)/4ᵐ. "
                    + "Konno's Hadamard return series gives the same coefficients. The matrix has Gram matrix 2I. "
                    + "Thus each unit initial state gives 2m−1 equal, positive weights and no others. "
                    + "The all-time condition includes time eight.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Entry(string declaration, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("sojourn-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula AmplitudeFormula()
    {
        var n = Id("n");
        var k = Id("k");
        var w = Id("w");
        return All("U", Coin, All("n", N, All("k", N,
            Eqn(Call("amplitude", U, n, k), IndexedSum(
                Seq(w, Sp, InMacro, Sp, Call("returningWords", n, k)), Call("wordOperator", U, w))))));
    }

    private static Formula WeightFormula()
    {
        var n = Id("n");
        var k = Id("k");
        return All("U", Coin, All("phi", Vector, All("n", N, All("k", N,
            Eqn(Call("weight", U, Id("phi"), n, k), new Formula.Power(
                Seq(Vert, Sp, Call("amplitude", U, n, k), Sp, Id("phi"), Sp, Vert), Num(2)))))));
    }

    private static Formula UniformFormula()
    {
        var m = Id("m");
        var k = Id("k");
        var phi = Id("phi");
        var time = Mul(Num(4), m);
        var total = IndexedSum(Seq(Num(0), Sp, Leq, Sp, Id("j"), Sp, Leq, Sp, time),
            Call("weight", U, phi, time, Id("j")));
        var support = Logic(Lt(Num(0), k), FormulaLogicOperator.And,
            Logic(Lt(k, time), FormulaLogicOperator.And, Call("Even", k)));
        var value = Seq(Operatorname, Grp(Id("if")), Sp, support, Sp, Operatorname, Grp(Id("then")), Sp,
            Frac(Num(1), Sub(Mul(Num(2), m), Num(1))), Sp, Operatorname, Grp(Id("else")), Sp, Num(0));
        return All("U", Coin, All("phi", Vector, All("m", N,
            Logic(Call("exactUniform", U, phi, m), FormulaLogicOperator.Iff,
                Seq(Operatorname, Grp(Id("let")), Sp, Id("T"), Sp, Eq, Sp, total, Sp, Operatorname,
                    Grp(Id("in")), Sp, Logic(Lt(Num(0), Id("T")), FormulaLogicOperator.And,
                        All("k", N, Eqn(Frac(Call("weight", U, phi, time, k), Id("T")), value))))))));
    }

    private static Formula RigidityFormula()
    {
        var i = Id("i");
        var j = Id("j");
        var phi = Id("phi");
        var m = Id("m");
        var balance = All("i", FinTwo, All("j", FinTwo,
            Eqn(Seq(Lvert, Sp, Call("U", i, j), Sp, Rvert), Frac(Num(1), Seq(Sqrt, Grp(Num(2)))))));
        var allTimes = All("m", N, Logic(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThanOrEqual, m),
            FormulaLogicOperator.Implies, Call("exactUniform", U, phi, m)));
        var hypotheses = Logic(Eqn(Mul(new Formula.Power(U, Id("H")), U), Num(1)), FormulaLogicOperator.And,
            Eqn(IndexedSum(Seq(i, Sp, InMacro, Sp, FinTwo), SqNorm(Call("phi", i))), Num(1)));
        return All("U", Coin, All("phi", Vector, Logic(hypotheses, FormulaLogicOperator.Implies,
            Logic(Logic(Call("exactUniform", U, phi, Num(2)), FormulaLogicOperator.Iff, balance),
                FormulaLogicOperator.And, Logic(balance, FormulaLogicOperator.Iff, allTimes)))));
    }

    private static Formula IndexedSum(Formula index, Formula summand) => Seq(new Formula.Subscript(Sum, index), Sp, summand);
    private static Formula SqNorm(Formula value) => new Formula.Power(Seq(Lvert, Sp, value, Sp, Rvert), Num(2));
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Id(string name) => DefinitionDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
}
