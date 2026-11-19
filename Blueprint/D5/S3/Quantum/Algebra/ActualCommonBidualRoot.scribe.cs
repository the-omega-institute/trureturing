using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class ActualCommonBidualRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One positive element of the real first-Arens bidual has one common root realizing all its canonical GNS square roots.",
        H("Common positive roots in the first-Arens bidual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-common-root"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/ActualCommonBidualRoot.exists_common_root"),
                H("A single bidual root for every actual positive reading"),
                StatementSource.FromAuthor(Disp(Statement(false))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let V be any real normed space, possibly incomplete. Let A have the classes CStarAlgebra A, PartialOrder A and StarOrderedRing A. Let i be a real linear isometry from V into A with self-adjoint values. Let S be a bounded real bilinear product on V satisfying i(S(x,y))=(i(x)i(y)+i(y)i(x))/2, and let u be an original vector with i(u)=1. There is no assumption that i(V) is closed or equals the full self-adjoint part of A.")),
                    Paragraph(Text("M means literally StrongDual real (StrongDual real V), with its canonical norm. Write j for the canonical inclusion of V into M. The product is the first-Arens extension arens(S,F,G)(phi)=F(G composed with rows(S,phi)); rows(S,phi)(x)(y)=phi(S(x,y)). In particular F remains the outer evaluation. arensBilinear bundles this same function as a real bilinear map.")),
                    Paragraph(Text("For each unnormalized positive complex-linear functional psi on A, the space psi.GNS and its canonical representation pi_psi define coefficient(xi,eta)(x)=inner(xi,pi_psi(i(x))eta). The actual operator B_psi(F)=gnsLinear(i,hi,psi)(F) is determined by inner(xi,B_psi(F)eta)=F(realPart composed with coefficient(xi,eta))+I F(imaginaryPart composed with coefficient(xi,eta)). It is self-adjoint and has norm at most norm(F). The representation is real-linear in F; psi is an index and is not a linear variable.")),
                    Paragraph(Text("Positive(i,hi,F) means that B_psi(F) is nonnegative for every actual positive psi. For each such F there is one G in this same M with arens(S,G,G)=F, norm(G) squared=norm(F), and Positive(i,hi,G). Moreover G belongs to generated(arensBilinear(S),j(u),F), the norm closure of the real span of the existing Jordan powers of F with zeroth power j(u). For every psi simultaneously, B_psi(G)=cfc(Real.sqrt,B_psi(F)). The functions cfc and Real.sqrt have their pinned Mathlib meanings.")),
                    Paragraph(Text("The coefficient operators come from the bounded Hermitian form and the Hilbert-space duality theorem. CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive decomposes every real functional on the original isometric image as the difference of two ambient positive continuous functionals, with total unit mass equal to its norm. Their actual cyclic-vector coefficients imply joint detection of the canonical bidual norm and separation of its elements. No positive mass is divided out.")),
                    Paragraph(Text("Original Jordan compatibility first gives the actual first-Arens product identity in every same-psi representation. Induction sends existing Jordan powers to associative operator powers. Each scalar polynomial q then gives one element q(F) in M whose psi reading is the operator polynomial q(B_psi(F)). The same family also gives the square-norm identity norm(arens(S,G,G))=norm(G) squared.")),
                    Paragraph(Text("Put R=norm(F). All spectra of B_psi(F) lie in [0,R]. Mathlib's exists_polynomial_near_of_continuousOn supplies real polynomials q_n approximating the scalar square root on that interval with error at most (1/2)^n. This sequence is chosen before psi. The CFC polynomial and norm identities bound norm(B_psi(q_n(F))-cfc(Real.sqrt,B_psi(F))) by the same error for every psi. Joint norm detection makes q_n(F) Cauchy in the actual M, and completeness of this bidual supplies one limit G. Continuity of each actual reading identifies its value with the designated operator root.")),
                    Paragraph(Text("The common readings and their product identity identify arens(S,G,G) with F. The square-norm identity gives the stated norm of G, operator CFC gives positivity, and closedness of the generated subspace preserves membership at the limit. If F=0 the witness is G=0. Zero functionals, zero GNS spaces and the zero ambient algebra remain in scope. Completeness of V, separability, norm attainment, normality of the original functionals, and closure of an operator image under square roots are not premises.")),
                    Paragraph(Text("The construction composes classical Hilbert duality, positive Hahn-Banach extension, scalar polynomial approximation and operator continuous functional calculus. No literary novelty is claimed for those tools. The root lies in the mathematical bidual; it does not supply an original input in V or a physical preparation. The full original signed overlap budget and the identification of the original coset slope with the kernel response require their own original-response arguments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-iff-square"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/ActualCommonBidualRoot.quadratic_iff_square"),
                H("Actual nonnegative quadratic readings are exactly bidual squares"),
                StatementSource.FromAuthor(Disp(Statement(true))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under exactly the same V,A,i,hi,S,hS,u,hu hypotheses, an arbitrary F in M has nonnegative real quadratic reading inner(v,B_psi(F)v) for every positive psi and every v in psi.GNS if and only if F=arens(S,G,G) for some G in M. The inner product is linear in its second argument.")),
                    Paragraph(Text("Self-adjointness identifies these quadratic inequalities with Positive(i,hi,F). The forward implication consumes the single common-root construction. For the reverse implication the actual product formula sends arens(S,G,G) to B_psi(G) squared, which is nonnegative because B_psi(G) is self-adjoint. All degeneracies and unnormalized readings have the same scope as in the root theorem."))),
                DescribeRole.Theorem))));

    private static Formula Statement(bool quadratic)
    {
        var V = F.Id("V"); var A = F.Id("A"); var i = F.Id("i"); var hi = F.Id("hi");
        var S = F.Id("S"); var u = F.Id("u"); var f = F.Id("F"); var g = F.Id("G");
        var psi = F.Id("psi"); var v = F.Id("v"); var x = F.Id("x"); var y = F.Id("y");
        var real = Call("Real"); var complex = Call("Complex");
        var M = Call("StrongDual", real, Call("StrongDual", real, V));
        Formula B(Formula z) => Apply(Call("gnsLinear", i, hi, psi), z);
        var square = Equal(Call("arens", S, g, g), f);
        var existsSquare = Exists("G", M, square);
        var positive = Call("Positive", i, hi, f);
        var quadraticReadings = All("psi", Call("PositiveLinearMap", complex, A, complex),
            All("v", Call("GNS", psi), Call("Le", Num(0),
                Call("re", Call("inner", complex, v, Apply(B(f), v))))));
        var generated = Call("generated", Call("arensBilinear", S),
            Apply(Call("inclusionInDoubleDual", real, V), u), f);
        var common = All("psi", Call("PositiveLinearMap", complex, A, complex),
            Equal(B(g), Call("cfc", Seq(F.Id("Real"), Dot, F.Id("sqrt")), B(f))));
        var rootResult = Exists("G", M,
            And(square, And(Equal(Call("pow", Call("norm", g), Num(2)), Call("norm", f)),
                And(Call("Positive", i, hi, g), And(Call("Member", g, generated), common)))));
        Formula conclusion = quadratic
            ? new Formula.Logic(quadraticReadings, FormulaLogicOperator.Iff, existsSquare)
            : Imp(positive, rootResult);
        var product = All("x", V, All("y", V,
            Equal(Apply(i, Apply(Apply(S, x), y)),
                Call("smul", Call("Divide", Num(1), Num(2)),
                    Call("Add", Call("Multiply", Apply(i, x), Apply(i, y)),
                        Call("Multiply", Apply(i, y), Apply(i, x)))))));
        var body = All("S", Call("ContinuousBilinearMap", real, V, V, V),
            Imp(product, All("u", V, Imp(Equal(Apply(i, u), Call("one", A)), All("F", M, conclusion)))));
        body = All("i", Call("LinearIsometry", real, V, A),
            All("hi", All("x", V, Call("IsSelfAdjoint", Apply(i, x))), body));
        body = All("A", Seq(Call("Type"), Star),
            Instance(Call("CStarAlgebra", A), Instance(Call("PartialOrder", A),
                Instance(Call("StarOrderedRing", A), body))));
        return All("V", Seq(Call("Type"), Star), Instance(Call("NormedAddCommGroup", V),
            Instance(Call("NormedSpace", real, V), body)));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Apply(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
