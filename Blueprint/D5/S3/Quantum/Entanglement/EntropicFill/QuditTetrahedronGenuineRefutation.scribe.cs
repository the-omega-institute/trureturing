using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntropicFill;

internal sealed class QuditTetrahedronGenuineRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/xieyounismeieberly2024journey");

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Type => F.Id("Type");
    private static Formula Four => Fin(D(4));
    private static Formula Six => Fin(D(6));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }

        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula QCall(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Matrix(Formula rows, Formula columns, Formula field) =>
        Call("Matrix", rows, columns, field);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Neg(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula Sqrt(Formula value) => QCall(Qualified("Real", "sqrt"), value);
    private static Formula Rpow(Formula value, Formula exponent) =>
        QCall(Qualified("Real", "rpow"), value, exponent);
    private static Formula Star(Formula value) => Call("star", value);
    private static Formula Ite(Formula condition, Formula yes, Formula no) =>
        Call("ite", condition, yes, no);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, F.Eq, Sp, value, Semi, Sp, body);
    private static Formula RealNumeral(byte value) => Typed(D(value), Real);
    private static Formula ComplexNumeral(byte value) => Typed(D(value), Complex);
    private static Formula FinNumeral(byte value, Formula size) => Typed(D(value), size);
    private static Formula Prime => Seq(F.Id("a"), Apos);

    private static Formula Rho1Formula()
    {
        Formula d = F.Id("d"), psi = Psi, i = F.Id("i"), a = F.Id("a");
        Formula matrix = Matrix(Fin(d), Fin(d), Complex);
        Formula coefficient = Arrow(Arrow(Four, Fin(d)), Complex);
        Formula update = QCall(Qualified("Function", "update"), F.Id("x"), i, Prime);
        Formula summand = Ite(Eq(App(F.Id("x"), i), a),
            Mul(App(psi, F.Id("x")), Star(App(psi, update))), ComplexNumeral(0));
        Formula body = Eq(Call("rho1", psi, i, a, Prime),
            SumOver(F.Id("x"), Arrow(Four, Fin(d)), summand));
        return All(d, Nat, All(psi, coefficient, All(i, Four,
            All(a, Fin(d), All(Prime, Fin(d), body)))));
    }

    private static Formula Rho2Formula()
    {
        Formula d = F.Id("d"), psi = Psi, i = F.Id("i"), j = F.Id("j"), a = F.Id("a");
        Formula pair = Product(Fin(d), Fin(d));
        Formula coefficient = Arrow(Arrow(Four, Fin(d)), Complex);
        Formula left = QCall(Qualified("Prod", "fst"), a);
        Formula right = QCall(Qualified("Prod", "snd"), a);
        Formula leftPrime = QCall(Qualified("Prod", "fst"), Prime);
        Formula rightPrime = QCall(Qualified("Prod", "snd"), Prime);
        Formula updated = QCall(Qualified("Function", "update"),
            QCall(Qualified("Function", "update"), F.Id("x"), i, leftPrime), j, rightPrime);
        Formula condition = And(Eq(App(F.Id("x"), i), left), Eq(App(F.Id("x"), j), right));
        Formula summand = Ite(condition,
            Mul(App(psi, F.Id("x")), Star(App(psi, updated))), ComplexNumeral(0));
        Formula body = Eq(Call("rho2", psi, i, j, a, Prime),
            SumOver(F.Id("x"), Arrow(Four, Fin(d)), summand));
        return All(d, Nat, All(psi, coefficient, All(i, Four, All(j, Four,
            All(a, pair, All(Prime, pair, body))))));
    }

    private static Formula Entropy2Formula()
    {
        Formula n = F.Id("n"), rho = Rho;
        Formula matrix = Matrix(n, n, Complex);
        Formula body = Eq(Call("entropy2", rho),
            Div(Call("entropy", rho), QCall(Qualified("Real", "log"), RealNumeral(2))));
        return All(n, Type, Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            Seq(OpenBracket, Call("DecidableEq", n), CloseBracket, Sp,
                All(rho, matrix, body))));
    }

    private static Formula BiseparableFormula()
    {
        Formula d = F.Id("d"), psi = Psi, x = F.Id("x"), y = F.Id("y"), i = F.Id("i");
        Formula state = Arrow(Four, Fin(d));
        Formula stateToComplex = Arrow(state, Complex);
        Formula X = F.Id("X"), phi = Varphi, chi = F.Id("chi");
        Formula complement = QCall(Qualified("Compl", "compl"), X);
        Formula inX = new Formula.Relation(i, FormulaRelationOperator.MemberOf, X);
        Formula notInX = new Formula.Not(Parenthesized(inX));
        Formula phiCondition = All(i, Four, Imp(inX, Eq(App(x, i), App(y, i))));
        Formula chiCondition = All(i, Four, Imp(notInX, Eq(App(x, i), App(y, i))));
        Formula phiDepends = All(x, state, All(y, state,
            Imp(phiCondition, Eq(App(phi, x), App(phi, y)))));
        Formula chiDepends = All(x, state, All(y, state,
            Imp(chiCondition, Eq(App(chi, x), App(chi, y)))));
        Formula factors = And(phiDepends, And(chiDepends,
            All(x, state, Eq(App(psi, x), Mul(App(phi, x), App(chi, x))))));
        Formula body = Some(X, Call("Finset", Four),
            And(QCall(Qualified("Finset", "Nonempty"), X), And(QCall(Qualified("Finset", "Nonempty"), complement),
                Some(phi, stateToComplex, Some(chi, stateToComplex, factors)))));
        return All(d, Nat, All(psi, stateToComplex, Eq(Call("Biseparable", psi), body)));
    }

    private static Formula AdmissibleFillFormula()
    {
        Formula d = F.Id("d"), psi = Psi, sigma = SigmaLower, ell = F.Id("ell"), k = F.Id("k");
        Formula state = Arrow(Four, Fin(d));
        Formula stateToComplex = Arrow(state, Complex);
        Formula sigmaType = Arrow(Six, Real);
        Func<byte, Formula> entropyOne = index => Call("entropy2",
            Call("rho1", psi, FinNumeral(index, Four)));
        Func<byte, byte, Formula> entropyTwo = (i, j) => Call("entropy2",
            Call("rho2", psi, FinNumeral(i, Four), FinNumeral(j, Four)));
        Func<byte, Formula> s = index => App(sigma, FinNumeral(index, Six));
        Formula nonnegative = All(k, Six, Le(RealNumeral(0), App(sigma, k)));
        Formula faceA = Eq(Add(Add(s(0), s(1)), s(2)), entropyOne(0));
        Formula faceB = Eq(Add(Add(s(0), s(3)), s(4)), entropyOne(1));
        Formula faceC = Eq(Add(Add(s(1), s(3)), s(5)), entropyOne(2));
        Formula faceD = Eq(Add(Add(s(2), s(4)), s(5)), entropyOne(3));
        Formula p = Sqrt(Mul(s(0), s(5))), q = Sqrt(Mul(s(1), s(4))), r = Sqrt(Mul(s(2), s(3)));
        Formula radicalA = Eq(Add(Add(Neg(p), q), r), Mul(ell, entropyTwo(0, 1)));
        Formula radicalB = Eq(Add(Add(p, Neg(q)), r), Mul(ell, entropyTwo(0, 2)));
        Formula radicalC = Eq(Add(Add(p, q), Neg(r)), Mul(ell, entropyTwo(0, 3)));
        Formula body = And(nonnegative, And(faceA, And(faceB, And(faceC,
            And(faceD, And(radicalA, And(radicalB, radicalC)))))));
        return All(d, Nat, All(psi, stateToComplex, All(sigma, sigmaType, All(ell, Real,
            Eq(Call("AdmissibleFill", psi, sigma, ell), body)))));
    }

    private static Formula VolumeFormula()
    {
        Formula sigma = SigmaLower;
        Func<byte, Formula> s = index => App(sigma, FinNumeral(index, Six));
        Formula p = Sqrt(Mul(s(0), s(5))), q = Sqrt(Mul(s(1), s(4))), r = Sqrt(Mul(s(2), s(3)));
        Formula total = SumOver(F.Id("k"), Six, App(sigma, F.Id("k")));
        Formula radicand = Mul(Mul(Mul(Add(Add(p, q), r), Add(Add(Neg(p), q), r)),
            Add(Add(p, Neg(q)), r)), Add(Add(p, q), Neg(r)));
        Formula pVar = F.Id("p"), qVar = F.Id("q"), rVar = F.Id("r");
        Formula value = Mul(Mul(Div(Sqrt(RealNumeral(2)), RealNumeral(3)),
            Sqrt(Mul(RealNumeral(2), total))),
            Rpow(Mul(Mul(Mul(Add(Add(pVar, qVar), rVar), Add(Add(Neg(pVar), qVar), rVar)),
                Add(Add(pVar, Neg(qVar)), rVar)), Add(Add(pVar, qVar), Neg(rVar))),
                Div(RealNumeral(1), RealNumeral(4))));
        Formula body = Let("p", p, Let("q", q, Let("r", r, value)));
        return All(sigma, Arrow(Six, Real), Eq(Call("volume", sigma), body));
    }

    private static Formula ClaimBody()
    {
        Formula d = F.Id("d"), psi = Psi, sigma = SigmaLower, ell = F.Id("ell");
        Formula state = Arrow(Four, Fin(d));
        Formula stateToComplex = Arrow(state, Complex);
        Formula sigmaType = Arrow(Six, Real);
        Formula normalized = Eq(SumOver(F.Id("x"), state, Pow(Norm(App(psi, F.Id("x"))),
            Typed(D(2), Nat))), RealNumeral(1));
        Formula hasFill = Some(sigma, sigmaType, Some(ell, Real,
            Call("AdmissibleFill", psi, sigma, ell)));
        Formula allZero = All(sigma, sigmaType, All(ell, Real,
            Imp(Call("AdmissibleFill", psi, sigma, ell),
                Eq(Call("volume", sigma), RealNumeral(0)))));
        return All(d, Nat, Imp(Le(Typed(D(2), Nat), d), All(psi, stateToComplex,
            Imp(normalized, Imp(hasFill, Imp(allZero, Call("Biseparable", psi)))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eight-level four-party pure state has an admissible zero-volume fill but is not biseparable, refuting the qudit genuine-entanglement claim.",
        H("A qudit counterexample to genuine entropic tetrahedra"),
        Blocks(
            Describe.Lean(DescribeId.Create("qudit-rho1"), DeclarationHandle.Create(Module + ".rho1"),
                H("One-party reduced density matrix"), StatementSource.FromAuthor(Disp(Rho1Formula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For a four-party coefficient function ψ, rho1 ψ i is the reduced density matrix of party i in the computational basis. Its (a,a') entry sums ψ(x) times the conjugate of the coefficient obtained by replacing the i-th coordinate of x by a', over all basis labels x whose i-th coordinate equals a."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qudit-rho2"), DeclarationHandle.Create(Module + ".rho2"),
                H("Two-party reduced density matrix"), StatementSource.FromAuthor(Disp(Rho2Formula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For distinct parties i and j, rho2 ψ i j is the two-party reduced density matrix. The entry indexed by (a,a') sums the coefficient product over labels whose i and j coordinates are the two components of a, replacing those coordinates by the components of a'."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qudit-entropy2"), DeclarationHandle.Create(Module + ".entropy2"),
                H("Base-two spectral entropy"), StatementSource.FromAuthor(Disp(Entropy2Formula())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "entropy2 divides the repository's natural-log spectral entropy by the natural logarithm of the real number 2, giving the base-two von Neumann entropy used by the source (TeX lines 65 and 107)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qudit-biseparable"), DeclarationHandle.Create(Module + ".Biseparable"),
                H("Biseparability across a proper cut"), StatementSource.FromAuthor(Disp(BiseparableFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Biseparable ψ holds when a nonempty proper finite set X of parties admits factors φ and χ, with φ depending only on coordinates in X, χ depending only on coordinates outside X, and ψ equal to their pointwise product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qudit-admissible-fill"), DeclarationHandle.Create(Module + ".AdmissibleFill"),
                H("Admissible entropic fill"), StatementSource.FromAuthor(Disp(AdmissibleFillFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "An admissible fill consists of six nonnegative real coordinates and a real parameter ell. The four sums of three coordinates equal the four one-party entropies, and the three signed radical sums equal ell times the two-party entropies. The coordinate order is AB, AC, AD, BC, BD, CD, as in the source's face and radical equations (TeX lines 103–121)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qudit-volume"), DeclarationHandle.Create(Module + ".volume"),
                H("Entropic tetrahedron volume"), StatementSource.FromAuthor(Disp(VolumeFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The volume uses p, q and r for the square roots of the products of opposite coordinate pairs. It is sqrt(2)/3 times the square root of twice the total coordinate sum, multiplied by the one-fourth real power of the four Heron-type factors. This is the source volume formula (TeX lines 91–101)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qudit-genuine-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The qudit genuine-entanglement claim"), StatementSource.FromAuthor(Disp(Eq(Named("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every natural d at least 2 and every unit four-party state ψ, if an admissible fill exists and every admissible fill has zero volume, then ψ is biseparable. This is the formal version of the source's scalability conjecture that the tetrahedron measure is a genuine four-qudit measure (TeX lines 218–220)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qudit-genuine-result"), DeclarationHandle.Create(Module + ".result"),
                H("The qudit claim is false"), StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Use the eight-level state supported on the labels (4b+2c+d,b,c,d), with b, c and d in {0,1}, and amplitude 1/sqrt(8) on each supported label. The support-label bijection has eight terms, so the squared norm sum is one.")),
                    Paragraph(Text("Summing the reduced-matrix entries gives the identity matrix divided by 8 for party A and a diagonal matrix with two entries 1/2 and six entries zero for each of B, C and D. The base-two entropies are therefore 3, 1, 1 and 1.")),
                    Paragraph(Text("Subtract the A face equation from the sum of the other three face equations. Nonnegativity forces the BC, BD and CD coordinates to vanish, and the face equations then force AB, AC and AD to equal 1. The tuple (1,1,1,0,0,0) with ell equal to zero satisfies all three radical equations, so an admissible fill exists. Every radical factor in the volume is zero, hence the volume is zero.")),
                    Paragraph(Text("If the state factored across a nonempty proper cut, the resulting product-minor identity would hold for every pair of basis labels. Applying it to the three pairs formed from the zero label and the labels 4, 2 and 1, then checking the membership choices for all four parties, contradicts the support equations for every proper cut. Thus the state is not biseparable.")),
                    Paragraph(Text("Applying the claimed implication at d equal to 8 to this normalized state, its admissible fill and its zero-volume property would give biseparability, contradicting the preceding minor argument. Therefore the full claim is false."))), DescribeRole.Theorem)
        )));
}
