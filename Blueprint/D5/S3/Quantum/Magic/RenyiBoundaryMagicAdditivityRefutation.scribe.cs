using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class RenyiBoundaryMagicAdditivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/rubboli2024magicadditivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary alpha-z Rényi magic additivity fails for a pair of three-qubit states at alpha = 2 and z = 1.",
        H("Boundary Rényi magic additivity"), Blocks(
            Node("support-le", "Support inclusion", "SupportLE", SupportFormula(),
                "Every vector annihilated by sigma is annihilated by rho. For positive matrices this is the support inclusion used in Eq. (2): the support of rho lies in the support of sigma.",
                DescribeRole.Definition),
            Node("log-two", "Base-two logarithms", "log2",
                All("x", Reals(), Equal(Local("log2", X("x")),
                    At(Qualified("Real", "logb"), RealTwo(), X("x")))),
                "The logarithm is Real.logb with base 2. The quantum relative entropies of §2 are measured with base-two logarithms.",
                DescribeRole.Definition),
            Node("dpi", "The data-processing region", "DPI", DpiFormula(),
                "The region D in §2 requires z > 0 and includes the three displayed alpha-z ranges together with the line alpha = 1.",
                DescribeRole.Definition),
            Node("qaz", "The spectral-power trace", "Qaz", QazFormula(),
                "The trace expression in Eq. (2) sandwiches the sigma power between two rho powers and then raises the product to z. Each matrix power uses Matrix.IsHermitian.cfc with the real function t ↦ t^x when the matrix is Hermitian, and is the zero matrix otherwise. Real powers use Real.rpow. The outer trace is its real part. This total definition applies to arbitrary operators; on positive states it gives the spectral expression of §2.",
                DescribeRole.Definition),
            Node("daz", "The alpha-z divergence and its support guards", "Daz", DazFormula(),
                "Equation (2) assigns a finite expression when alpha < 1 and rho times sigma is nonzero, or when the support inclusion holds; otherwise it assigns ⊤ in EReal, the value +∞. At alpha = 1, the supported branch is the Umegaki expression from Eq. (8), divided by Real.log 2, and failure of support inclusion again gives ⊤. Matrix logarithms use Matrix.IsHermitian.cfc with Real.log on Hermitian matrices and zero otherwise. Real.toEReal embeds each real-valued branch in EReal. These formulas state the total definition, including inputs outside the parameter region or state domain.",
                DescribeRole.Definition),
            Node("magic", "The infimum over stabilizer states", "magic", MagicFormula(),
                "Equation (10) takes the infimum of the alpha-z divergence over mixed stabilizer states. Here sInf is taken in EReal over the image of STAB n under the divergence with rho fixed.",
                DescribeRole.Definition),
            Node("claim", "Boundary additivity for two and three qubits", "claim",
                IffOf(Name("claim"), ClaimFormula()),
                "Section 5 asks whether all alpha-z magic monotones with |(1 − alpha)/z| = 1 are additive for all two- and three-qubit states. This proposition quantifies over the data-processing region, both permitted subsystem sizes independently, and all density matrices on those subsystems.",
                DescribeRole.Definition),
            Node("result", "A three-qubit pair refutes boundary additivity", "result",
                new Formula.Not(Name("claim")),
                "The universal statement in §5 is false. At alpha = 2 and z = 1, take rho = (11I + 4S)/88 and its entrywise conjugate, with S from D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape. The completed-square inequality and the three-qubit polar bound give each marginal magic value a lower bound of log2(1015/726). A six-qubit stabilizer mixture of the product comparison state and three Bell pairs gives a joint value strictly below twice that bound. Singular comparison states have divergence +∞ by the support guard. The positive definite comparisons use the trace of rho squared times the inverse comparison matrix. These bounds contradict the claimed equality for this pair.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        )));

    private static Formula SupportFormula() => All("n", Naturals(), All("rho", Op(X("n")),
        All("sigma", Op(X("n")), IffOf(Local("SupportLE", X("rho"), X("sigma")),
            All("v", Arrow(Bits(X("n")), Complexes()),
                Imp(Equal(At(Qualified("Matrix", "mulVec"), X("sigma"), X("v")),
                        Typed(Num(0), Arrow(Bits(X("n")), Complexes()))),
                    Equal(At(Qualified("Matrix", "mulVec"), X("rho"), X("v")),
                        Typed(Num(0), Arrow(Bits(X("n")), Complexes())))))))));

    private static Formula DpiFormula()
    {
        Formula alpha = X("alpha"), z = X("z");
        Formula below = And(LT(Num(0), alpha), And(LT(alpha, Num(1)),
            LE(Call("max", alpha, Sub(Num(1), alpha)), z)));
        Formula middle = And(LT(Num(1), alpha), And(LE(alpha, RealTwo()),
            And(LE(Fraction(alpha, RealTwo()), z), LE(z, alpha))));
        Formula above = And(LE(RealTwo(), alpha), And(LE(Sub(alpha, Num(1)), z), LE(z, alpha)));
        return All("alpha", Reals(), All("z", Reals(), IffOf(Local("DPI", alpha, z),
            And(LT(Num(0), z), Or(below, Or(Equal(alpha, Num(1)), Or(middle, above)))))));
    }

    private static Formula QazFormula()
    {
        Formula rhoPower = HermitianPower(X("rho"), Fraction(X("alpha"), Mul(RealTwo(), X("z"))));
        Formula sigmaPower = HermitianPower(X("sigma"), Fraction(Sub(Num(1), X("alpha")), X("z")));
        Formula product = Mul(Mul(rhoPower, sigmaPower), rhoPower);
        return Operators(Equal(Local("Qaz", X("alpha"), X("z"), X("rho"), X("sigma")),
            Abstract("tr", HermitianPower(product, X("z")))));
    }

    private static Formula DazFormula()
    {
        Formula supported = Local("SupportLE", X("rho"), X("sigma"));
        Formula guard = Or(And(LT(X("alpha"), Num(1)),
            NE(Mul(X("rho"), X("sigma")), Typed(Num(0), Op(X("n"))))), supported);
        Formula umegaki = ToEReal(Fraction(Abstract("tr", Mul(X("rho"),
            Sub(HermitianLog(X("rho")), HermitianLog(X("sigma"))))),
            At(Qualified("Real", "log"), RealTwo())));
        Formula renyi = ToEReal(Fraction(Local("log2", Local("Qaz", X("alpha"), X("z"), X("rho"), X("sigma"))),
            Sub(X("alpha"), Num(1))));
        Formula body = Call("ite", Equal(X("alpha"), Num(1)),
            Call("ite", supported, umegaki, TopEReal()), Call("ite", guard, renyi, TopEReal()));
        return Operators(Equal(Typed(Local("Daz", X("alpha"), X("z"), X("rho"), X("sigma")), EReals()), body));
    }

    private static Formula MagicFormula() => All("n", Naturals(), All("alpha", Reals(),
        All("z", Reals(), All("rho", Op(X("n")),
            Equal(Typed(Local("magic", X("alpha"), X("z"), X("rho")), EReals()),
                Call("sInf", At(Qualified("Set", "image"),
                    LambdaOf("sigma", Op(X("n")), Local("Daz", X("alpha"), X("z"), X("rho"), X("sigma"))),
                    Abstract("STAB", X("n")))))))));

    private static Formula ClaimFormula()
    {
        Formula conclusion = Equal(Local("magic", X("alpha"), X("z"), Abstract("tensor", X("rho"), X("omega"))),
            Add(Local("magic", X("alpha"), X("z"), X("rho")), Local("magic", X("alpha"), X("z"), X("omega"))));
        Formula states = All("rho", Op(X("n")), All("omega", Op(X("m")),
            Imp(Abstract("IsState", X("rho")), Imp(Abstract("IsState", X("omega")), conclusion))));
        Formula dimensions = All("n", Naturals(), All("m", Naturals(),
            Imp(Or(Equal(X("n"), Num(2)), Equal(X("n"), Num(3))),
                Imp(Or(Equal(X("m"), Num(2)), Equal(X("m"), Num(3))), states))));
        return All("alpha", Reals(), All("z", Reals(), Imp(Local("DPI", X("alpha"), X("z")),
            Imp(Equal(new Formula.Absolute(Fraction(Sub(Num(1), X("alpha")), X("z"))), Num(1)), dimensions))));
    }

    private static Formula HermitianPower(Formula matrix, Formula exponent) => HermitianCalculus(matrix,
        LambdaOf("t", Reals(), At(Qualified("Real", "rpow"), X("t"), exponent)));
    private static Formula HermitianLog(Formula matrix) => HermitianCalculus(matrix, Qualified("Real", "log"));
    private static Formula HermitianCalculus(Formula matrix, Formula function) => Parenthesized(Seq(
        Mathrm, Grp(X("if")), Sp, Typed(X("h"), At(Qualified("Matrix", "IsHermitian"), matrix)),
        Sp, Mathrm, Grp(X("then")), Sp, At(Qualified("Matrix", "IsHermitian", "cfc"), X("h"), function),
        Sp, Mathrm, Grp(X("else")), Sp, Typed(Num(0), Op(X("n")))));
    private static Formula Operators(Formula body) => All("n", Naturals(), All("alpha", Reals(),
        All("z", Reals(), All("rho", Op(X("n")), All("sigma", Op(X("n")), body)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role,
            declaration == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("rubboli-takagi-tomamichel-2024-magic-additivity-refutation"),
                ResolutionKind.Refuted) : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        Formula value = X(parts[0]);
        for (int i = 1; i < parts.Length; i++) value = Seq(value, Dot, X(parts[i]));
        return Seq(Operatorname, Grp(value));
    }
    private static Formula Name(string name) => Qualified("D5", "S3", "Quantum", "Magic", "RenyiBoundaryMagicAdditivityRefutation", name);
    private static Formula Local(string name, params Formula[] args) => At(Name(name), args);
    private static Formula Abstract(string name, params Formula[] args) => At(Qualified("D5", "S3", "Quantum", "Magic", "ThreeQubitStabilizerPolarEscape", name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula RealTwo() => Typed(At(Qualified("Nat", "cast"), Typed(Num(2), Naturals())), Reals());
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula EReals() => Qualified("EReal");
    private static Formula Bits(Formula n) => Abstract("Bits", n);
    private static Formula Op(Formula n) => Abstract("Op", n);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula ToEReal(Formula value) => Typed(At(Qualified("Real", "toEReal"), value), EReals());
    private static Formula TopEReal() => Typed(Qualified("Top", "top"), EReals());
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula LambdaOf(string name, Formula domain, Formula body) => Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), domain), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
