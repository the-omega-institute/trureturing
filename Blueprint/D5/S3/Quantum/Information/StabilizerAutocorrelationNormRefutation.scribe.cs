using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class StabilizerAutocorrelationNormRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Fourier Clifford changes the Euclidean operator norm of the six-by-five matrix of MUB probability autocorrelations.",
        H("Clifford invariance fails for the autocorrelation operator norm"),
        Blocks(
            Entry("omega", Equal(V("omega"), Call("exp", Div(Mul(Mul(D(2), Pi), V("i")), D(5)))),
                "The positive fifth root of unity is exp(2 pi i/5).", DescribeRole.Definition),
            Entry("tau", Equal(V("tau"), Pow(V("omega"), D(3))),
                "The odd-dimensional Weyl phase is the third power of omega.", DescribeRole.Definition),
            Entry("shift", All("i", Five, All("j", Five,
                Equal(Apply("shift", V("i"), V("j")),
                    Call("ite", Equal(V("i"), Add(V("j"), D(1))), D(1), D(0))))),
                "The shift sends the computational vector numbered j to the vector numbered j+1. All index arithmetic is modulo five.", DescribeRole.Definition),
            Entry("clock", All("i", Five, All("j", Five,
                Equal(Apply("clock", V("i"), V("j")),
                    Call("ite", Equal(V("i"), V("j")), Pow(V("omega"), Val(V("j"))), D(0))))),
                "The clock is diagonal with entry omega to the natural representative of j.", DescribeRole.Definition),
            Entry("displacement", All("p", Five, All("q", Five,
                Equal(Apply("displacement", V("p"), V("q")),
                    Mul(Pow(V("tau"), Mul(Val(V("p")), Val(V("q")))),
                        Mul(Pow(V("shift"), Val(V("p"))), Pow(V("clock"), Val(V("q")))))))),
                "The scalar factor multiplies the matrix product X^p Z^q, with X the shift and Z the clock.", DescribeRole.Definition),
            Entry("projector", ProjectorFormula(),
                "The six native spectral projector families are indexed by Option(Fin 5). None denotes infinity; some m denotes the line (mr,r). The outcome label j is the spectral label in the Fourier sum. These are the canonical Weyl--Heisenberg MUBs used in Stacey, SICs, the Stabilizer Polytope and Majorization, arXiv:2509.16819v1, Section III, with the construction cited there from Appleby--Dang--Fuchs.", DescribeRole.Definition),
            Entry("probability", All("psi", State, All("m", Bases, All("j", Five,
                Equal(Apply("probability", V("psi"), V("m"), V("j")),
                    Call("re", SumOver("i", Five,
                        Mul(Call("conj", Apply("psi", V("i"))),
                            SumOver("k", Five, Mul(Apply("projector", V("m"), V("j"), V("i"), V("k")),
                                Apply("psi", V("k"))))))))))),
                "The probability is the real part of the expectation of the projector. On normalized states this is the Born probability.", DescribeRole.Definition),
            Entry("autocorr", All("psi", State, All("m", Bases, All("k", Five,
                Equal(Apply("autocorr", V("psi"), V("m"), V("k")),
                    SumOver("j", Five, Mul(Apply("probability", V("psi"), V("m"), V("j")),
                        Apply("probability", V("psi"), V("m"), Add(V("j"), V("k"))))))))),
                "This is the real six-by-five matrix A of the source. In each row, k is a cyclic difference of the native outcome labels.", DescribeRole.Definition),
            Entry("IsClifford", CliffordFormula(),
                "A Clifford matrix is unitary in both orders and conjugates each Weyl generator to a displacement times a complex scalar of norm one. Dagger denotes conjugate transpose.", DescribeRole.Definition),
            Entry("claim", ClaimFormula(),
                "The proposed invariance says that every normalized pure state and every Clifford unitary have equal autocorrelation operator norms before and after the unitary. The norm is the ordinary Euclidean operator norm of the rectangular real matrix. This is a necessary assertion for the unrestricted family of unitarily invariant matrix-norm magic monotones proposed following Stacey's definition of A. The source says: Acting upon the state with a Clifford unitary can at most permute the rows and columns of the matrix A.", DescribeRole.Definition),
            Entry("fourier", All("i", Five, All("j", Five,
                Equal(Apply("fourier", V("i"), V("j")),
                    Div(Pow(V("omega"), Val(Mul(V("i"), V("j")))), Call("sqrt", D(5)))))),
                "The positive-exponent Fourier matrix is unitary and sends X to Z and Z to X inverse under conjugation.", DescribeRole.Definition),
            Entry("psi", All("j", Five, Equal(Apply("psi", V("j")),
                Call("ite", Or(Equal(V("j"), D(0)), Equal(V("j"), D(1))),
                    Div(D(1), Call("sqrt", D(2))), D(0)))),
                "The state has equal amplitudes 1/sqrt(2) in the first two coordinates and zero elsewhere.", DescribeRole.Definition),
            Entry("result", new Formula.Not(V("claim")),
                "For psi=(1,1,0,0,0)/sqrt(2), write s=sqrt(5), a=(1/2,1/4,0,0,1/4), b=(3/10,(7+s)/40,(7-s)/40,(7-s)/40,(7+s)/40), and c=(3/10,(7-s)/40,(7+s)/40,(7+s)/40,(7-s)/40). In the row order (0,1,2,3,4,infinity), A(psi) has rows (a,b,c,c,b,b), whereas A(F psi) has rows (b,b,b,b,b,a). The squared Frobenius norm of A(psi) transpose times A(psi) is (2961+19s)/1600, below 49/25. Hence the squared operator norm of A(psi) is below 7/5. The test vector b has squared length 9/40, and A(F psi)b has squared length (993+19s)/3200. Their ratio exceeds 7/5 since 2<s<3. Thus the two operator norms differ. A common permutation of all columns would preserve the operator norm; the Clifford action can permute differences differently in different rows. The statement concerns the proposed unrestricted norm family and does not refute Frobenius-norm invariance.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("stacey-autocorr-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Five => Call("Fin", D(5));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Bases => Call("Option", Five);
    private static Formula State => Seq(Five, To, Complex);
    private static Formula Matrices => Call("Matrix", Five, Five, Complex);
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Or, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula SumOver(string name, Formula type, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), InMacro, type)), Sp, term);
    private static Formula Adj(Formula x) => Call("conjTranspose", x);
    private static Formula Action(Formula u, Formula psi) => Call("mulVec", u, psi);
    private static Formula Norm(Formula x) => new Formula.Norm(x);

    private static Formula ProjectorFormula()
    {
        Formula r = V("r"), m = V("m"), j = V("j");
        Formula line = Call("Option.casesOn", m, Apply("displacement", r, D(0)),
            Seq(LambdaLower, V("q"), Mapsto, Apply("displacement", Mul(V("q"), r), r)));
        return All("m", Bases, All("j", Five,
            Equal(Apply("projector", m, j), Mul(Div(D(1), D(5)), SumOver("r", Five,
                Mul(Pow(V("omega"), Val(Mul(new Formula.Negate(j), r))), line))))));
    }

    private static Formula CliffordFormula()
    {
        Formula u = V("U"), c = V("c");
        Formula Image(string generator) => Some("p", Five, Some("q", Five, Some("c", Complex,
            And(Equal(Norm(c), D(1)), Equal(Mul(Mul(u, V(generator)), Adj(u)),
                Mul(c, Apply("displacement", V("p"), V("q"))))))));
        return All("U", Matrices, Equal(Apply("IsClifford", u),
            And(Equal(Mul(Adj(u), u), D(1)), And(Equal(Mul(u, Adj(u)), D(1)),
                And(Image("shift"), Image("clock"))))));
    }

    private static Formula ClaimFormula()
    {
        Formula psi = V("psi"), u = V("U");
        return Equal(V("claim"), All("psi", State,
            Imp(Equal(SumOver("i", Five, Call("normSq", Apply("psi", V("i")))), D(1)),
                All("U", Matrices, Imp(Apply("IsClifford", u),
                    Equal(Norm(Apply("autocorr", Action(u, psi))), Norm(Apply("autocorr", psi))))))));
    }
}
