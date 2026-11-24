using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaMatrixAndFractranDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran";

    public DocumentDefinition Create()
    {
        Formula a = F.Id("A"), b = F.Id("B"), e = F.Id("I");
        Formula u = F.Id("u"), g = F.Id("g"), h = F.Id("h");
        Formula p = F.Id("P"), n = F.Id("n"), m = F.Id("m"), r = F.Id("r");
        Formula k = F.Id("k"), t = F.Id("t");
        Formula matrix = F.Id("Mat2"), nat = F.Id("OmegaNat"), prog = F.Id("Program");
        Formula core = F.Id("Core"), generator = F.Id("Generator");
        Formula tr = Call("tr", a), det = Call("det", a), adj = Call("adj", a);
        Formula scalar = Call("scale", det, e);
        Formula split = Call("split5", Call("coordinates", g));
        Formula factors = Call("factors", g);
        Formula run = Call("run", p, k, n);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact integer matrices, modulo-five splitting and fraction programs for the OmegaMath architecture.",
            H("Integer matrices, Hurwitz units and exact fraction programs"),
            Blocks(
                Law("trace_mul_comm", "Cyclicity of the trace",
                    All(Equal(Call("tr", Mul(a, b)), Call("tr", Mul(b, a))), ("A", matrix), ("B", matrix)),
                    "Expanding the two traces gives the same four integer products."),
                Law("adjugate_identities", "The two adjugate identities",
                    All(And(Equal(Mul(a, adj), scalar), Equal(Mul(adj, a), scalar)), ("A", matrix)),
                    "The diagonal entries are the determinant. The off-diagonal entries vanish."),
                Law("cayley_hamilton", "The quadratic characteristic identity",
                    All(Equal(Add(Sub(Mul(a, a), Call("scale", tr, a)), scalar), D(0)), ("A", matrix)),
                    "Every matrix of size two with integer entries satisfies the monic quadratic determined by its trace and determinant."),
                Law("hurwitz_core_unit", "Norms of the twelve Hurwitz representatives",
                    All(Equal(Call("normSq", Call("doubled", u)), D(4)), ("u", core)),
                    "The four axial representatives have a single doubled coordinate equal to two. Each of the eight others has four doubled coordinates of magnitude one."),
                Law("mod_five_rank_one", "Rank-one splitting of the norm-five generators",
                    All(And(Equal(split, Call("outer",
                        Call("u", factors), Call("v", factors), Call("s", factors), Call("t", factors))),
                        Equal(Call("isZero", split), F.Id("false"))), ("g", generator)),
                    "The split sends i to the diagonal matrix with entries two and minus two. Each listed factorization is an outer product over residues modulo five."),
                Law("mod_five_product_zero", "Zero products among split generators",
                    All(Equal(Call("isZero", Call("mul5", split, Call("split5", Call("coordinates", h)))), Call("isOpposite", g, h)),
                        ("g", generator), ("h", generator)),
                    "Among the thirty-six ordered products, precisely the six ordered conjugate pairs vanish."),
                Law("fractran_step_iff", "The evaluator realizes the ordered transition relation",
                    All(Logic(Equal(Call("step", p, n), Call("some", m)), FormulaLogicOperator.Iff,
                        Call("Step", p, n, m)), ("P", prog), ("n", nat), ("m", nat)),
                    "A guard holds when the stored denominator divides the state. This is Conway's integral-product test for a reduced fraction. The first enabled rule multiplies the exact quotient by its positive numerator."),
                Law("fractran_deterministic", "Determinism of the transition relation",
                    All(If(And(Call("Step", p, n, m), Call("Step", p, n, r)), Equal(m, r)),
                        ("P", prog), ("n", nat), ("m", nat), ("r", nat)),
                    "Both transitions compute the same result of the ordered scan."),
                Law("fractran_positive", "Runs preserve positivity",
                    All(If(Rel(D(0), FormulaRelationOperator.LessThan, n),
                        Rel(D(0), FormulaRelationOperator.LessThan, run)),
                        ("P", prog), ("k", nat), ("n", nat)),
                    "An enabled positive denominator at a positive state gives a positive quotient. Every numerator is positive by construction."),
                Law("fractran_stable", "Runs stabilize at a halting state",
                    All(If(Call("Halts", p, run), Equal(Call("run", p, Add(k, t), n), run)),
                        ("P", prog), ("k", nat), ("n", nat), ("t", nat)),
                    "When every guard fails, another iteration returns the same state."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))], body));

    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula If(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);

    private static DocumentBlock.Describe Law(string selector, string title, Formula statement, string note) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-')), DeclarationHandle.Create($"{Module}.{selector}"),
            H(title), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(note))), DescribeRole.Theorem);
}
