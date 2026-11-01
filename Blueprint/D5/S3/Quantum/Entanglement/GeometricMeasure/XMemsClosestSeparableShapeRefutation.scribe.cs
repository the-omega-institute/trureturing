using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GeometricMeasure;

internal sealed class XMemsClosestSeparableShapeRefutationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Divergence/consiglioapollarowiesniak2022separability");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fully separable three-qubit state is closer to an X-MEMS than every fully separable state of the proposed shape.",
        H("A closest separable state need not have the proposed X-MEMS shape"),
        Blocks(
            Node("xmems", "xmems", "The low-branch X-MEMS matrix", XMemsFormula(),
                "The computational basis consists of functions from Fin n to Fin 2, with coordinate zero "
                + "the most significant bit. The diagonal is 1/(2^(n-1)+1) at every word whose first bit "
                + "is zero and at the all-one word, and zero elsewhere. The two opposite corners are "
                + "gamma and its complex conjugate. This is the low branch of the matrix in PRA_v2.tex, "
                + "lines 341-373, where f and g both equal 1/(N+1). The definition gives a matrix for "
                + "every natural n and complex gamma; the low-branch bound and n at least two occur in claim. "
                + "Subtraction n-1 is natural subtraction. Function.const denotes each constant bit string.",
                AssessedProvenance.FromLiterature(Source)),
            Node("css-shape", "cssShape", "The proposed matrix shape", CssShapeFormula(),
                "The all-zero and all-one diagonal entries are a/2. The other first-bit-zero entries "
                + "are b/(2^(n-1)-1), and the remaining diagonal entries are (1-a-b)/(2^(n-1)-1). "
                + "The opposite corners are d and its complex conjugate, and every other entry is zero. "
                + "This is equation (A11), PRA_v2.tex, lines 459-474. Each real diagonal expression is "
                + "included in the complex scalars by Complex.ofReal. The matrix is defined without "
                + "restrictions on its parameters; IsCssShape supplies the stated restrictions.",
                AssessedProvenance.FromLiterature(Source)),
            Node("is-css-shape", "IsCssShape", "The parameter restrictions", IsCssShapeFormula(),
                "A matrix has the proposed shape if it equals cssShape n a b d for real a and b "
                + "in the unit interval with a+b at most one, and complex d with norm at most a/2. "
                + "These are exactly the restrictions following equation (A11), PRA_v2.tex, line 474. "
                + "Full separability is a separate requirement.",
                AssessedProvenance.FromLiterature(Source)),
            Node("hs-sq", "hsSq", "Squared Hilbert-Schmidt distance", HsSqFormula(),
                "Apply the frozen D5.S3.Quantum.Tomography.RankOneContextCommutator.hilbertSchmidtSquare "
                + "to the matrix difference. Unfolding it gives the real part of the trace of that "
                + "difference conjugate-transpose multiplied by the difference. For density matrices this is "
                + "the squared Hilbert-Schmidt distance called D_HS in PRA_v2.tex, lines 70-84. "
                + "The formula also applies to arbitrary matrices, without a Hermitian hypothesis.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "A closest fully separable state of the proposed shape", ClaimFormula(),
                "For every n at least two and every complex gamma of norm at most 1/(2^(n-1)+1), "
                + "some fully separable matrix has the proposed shape and minimizes the squared "
                + "Hilbert-Schmidt distance to xmems n gamma among all fully separable matrices. "
                + "Full separability uses the frozen finite-mixture predicate "
                + "D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction.IsFullySeparableLocal, "
                + "applied to each matrix: it admits a finite mixture of products of local density "
                + "states with nonnegative real weights summing to one. Each local density state is "
                + "positive semidefinite with trace one. "
                + "This is the low-branch reading of the conjecture in PRA_v2.tex, lines 459-474, "
                + "using the closest-state definition at lines 80-93. It asserts attainment as well "
                + "as comparison with every fully separable matrix, and it places no further "
                + "restriction on the phase of gamma.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("xmems-css-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The three-qubit obstruction at gamma equal to 11/112"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First, the trace expression for hsSq equals the sum of the squared complex "
                        + "moduli of all entry differences. For three qubits, enumerate the eight "
                        + "binary words in order 000,001,010,011,100,101,110,111, denoted by indices "
                        + "0 through 7 in the following calculations.")),
                    Paragraph(Text(
                        "Consider a product P of three one-qubit density matrices. Put A_k equal "
                        + "to the real 00 diagonal entry of its kth factor and B_k equal to the real "
                        + "11 entry. These numbers are nonnegative, and positivity bounds the squared "
                        + "modulus of each local 01 entry by A_k B_k. Consequently Re(P_07) is at "
                        + "most sqrt(product of A_k B_k). For nonnegative u,v, the arithmetic-geometric "
                        + "mean inequality is supplied by the frozen "
                        + "D5.S3.Geometry.Hyperideal.GramDomainContraction.twice_sqrt_product_le_add. "
                        + "It gives sqrt(uv) at most (u+v)/2; applying it to u/3 and 3v "
                        + "also gives sqrt(uv) at most u/6+3v/2.")),
                    Paragraph(Text(
                        "Group the product under the square root as "
                        + "(A_0 A_1 B_2)(B_0 B_1 A_2). The weighted inequality then gives "
                        + "Re(P_07) at most P_11/6+3P_66/2. For a second bound, split the square root "
                        + "into sqrt(A_0 B_0) times sqrt(A_1 B_1 A_2 B_2). Bound the first factor "
                        + "by A_0/6+3B_0/2. For the term multiplied by A_0/6, bound the second "
                        + "factor by (A_1 A_2+B_1 B_2)/2; for the term multiplied by 3B_0/2, "
                        + "bound it by (A_1 B_2+B_1 A_2)/2. This yields Re(P_07) at most "
                        + "P_00/12+P_33/12+3P_55/4+3P_66/4. All displayed diagonal entries of P "
                        + "are real.")),
                    Paragraph(Text(
                        "Combine the first bound with weight 1/5 and the second with weight 4/5. "
                        + "The resulting inequality defines a convex half-space because real parts "
                        + "of matrix entries are real-linear. It contains every product of density "
                        + "matrices and therefore their real convex hull. The proof identifies this "
                        + "convex hull with the frozen finite-mixture full-separability predicate. "
                        + "For a fully separable "
                        + "matrix cssShape 3 a b d, write s=a/2, B=b/3, C=(1-a-b)/3, r=Re(d) "
                        + "and t=Im(d). Substitution gives r at most s/15+B/10+3C/2.")),
                    Paragraph(Text(
                        "Set rho=xmems 3 (11/112). Expanding its squared distance to cssShape 3 a b d "
                        + "gives 2(1/5-s)^2+3(1/5-B)^2+3C^2+2((11/112-r)^2+t^2). "
                        + "Since 2s+3B+3C=1, this equals 109/23520 plus "
                        + "2(s-3/16)^2+3(B-3/16)^2+3(C-1/48)^2+2(r-1/16)^2+2t^2 "
                        + "plus (s/15+B/10+3C/2-r)/7. Every additional term is nonnegative "
                        + "for a fully separable matrix of this shape. Its squared distance is "
                        + "therefore at least 109/23520.")),
                    Paragraph(Text(
                        "To construct a closer state, use the standard additive character chi "
                        + "of ZMod 3. For 0 at most u at most 1 and c in ZMod 3, use the frozen "
                        + "D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude "
                        + "at parameters 1-u and chi(c). Its coordinates are sqrt(u) and "
                        + "sqrt(1-u) chi(c). Its outer product with its conjugate is positive "
                        + "semidefinite; the frozen latitude_dot identity and "
                        + "star(chi(c)) chi(c)=1 give trace one. For a,b in "
                        + "ZMod 3, form the tensor product of these local densities at parameters "
                        + "(9/10,a), (199/400,b), and (199/400,-a-b).")),
                    Paragraph(Text(
                        "Let m(x) be the product of the three nonnegative coordinate magnitudes "
                        + "at a binary word x. The x,y entry of the preceding tensor product is "
                        + "m(x)m(y) chi(a u+b v), where u=x(0)-y(0)-x(2)+y(2) and "
                        + "v=x(1)-y(1)-x(2)+y(2), with each bit included in ZMod 3. Character "
                        + "orthogonality makes the sum over a,b equal to 9m(x)m(y) when u=v=0, "
                        + "and zero otherwise. Among binary words, u=v=0 holds exactly on the "
                        + "diagonal and at the two opposite corners. The diagonal magnitudes "
                        + "squared are products of 9/10 or 1/10 and two factors 199/400 or "
                        + "201/400; the opposite-corner magnitude product is 119997/1600000.")),
                    Paragraph(Text(
                        "Define a matrix T with diagonal "
                        + "(356409,359991,359991,363609,39601,39999,39999,360401)/1920000, "
                        + "opposite corners 119997/1920000, and all other entries zero. The "
                        + "character sum shows that T equals 5/54 times the sum of the nine "
                        + "product densities just constructed, plus 1/6 times the projector onto "
                        + "111. The latter is the product of the three local densities with "
                        + "u=0,c=0. Each row-average over b and then the average over a is fully "
                        + "separable by convexity. Taking weights 5/6 and 1/6 for that double "
                        + "average and the 111 projector proves that T is fully separable.")),
                    Paragraph(Text(
                        "Entrywise evaluation gives hsSq rho T = 417965512477/90316800000000, "
                        + "strictly below 109/23520. Finally, claim at n=3 and gamma=11/112, "
                        + "whose norm is at most 1/5, would supply a fully separable matrix sigma "
                        + "of the proposed shape with hsSq rho sigma at most hsSq rho T. The "
                        + "lower bound on every such sigma contradicts this strict inequality. "
                        + "This excludes the proposed shape for a closest fully separable state "
                        + "in this instance; it does not identify the actual closest state or "
                        + "address the high branch."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("consiglio-apollaro-wiesniak-2022-xmems-css-shape"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("xmems-css-" + id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula XMemsFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var gamma = GammaLower;
        var diagonal = If(Or(Equal(x, ConstantBit(1)), FirstBitZero(x)),
            Divide(Typed(D(1), Complexes), Add(Pow(Typed(D(2), Complexes), Exponent), Typed(D(1), Complexes))),
            Typed(D(0), Complexes));
        var entries = If(Equal(x, y), diagonal,
            If(And(Equal(x, ConstantBit(0)), Equal(y, ConstantBit(1))), gamma,
                If(And(Equal(x, ConstantBit(1)), Equal(y, ConstantBit(0))),
                    At(Qualified("Star", "star"), gamma), Typed(D(0), Complexes))));
        return All("n", Naturals, All("γ", Complexes,
            Equal(Typed(LocalCall("xmems", F.Id("n"), gamma), MatrixType),
                LambdaOf("x", Words, LambdaOf("y", Words, entries)))));
    }

    private static Formula CssShapeFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var a = F.Id("a");
        var b = F.Id("b");
        var d = F.Id("d");
        var denominator = Subtract(Pow(Typed(D(2), Reals), Exponent), Typed(D(1), Reals));
        var diagonal = If(Or(Equal(x, ConstantBit(0)), Equal(x, ConstantBit(1))),
            OfReal(Divide(a, Typed(D(2), Reals))),
            If(FirstBitZero(x), OfReal(Divide(b, denominator)),
                OfReal(Divide(Subtract(Subtract(Typed(D(1), Reals), a), b), denominator))));
        var entries = If(Equal(x, y), diagonal,
            If(And(Equal(x, ConstantBit(0)), Equal(y, ConstantBit(1))), d,
                If(And(Equal(x, ConstantBit(1)), Equal(y, ConstantBit(0))),
                    At(Qualified("Star", "star"), d), Typed(D(0), Complexes))));
        return All("n", Naturals, All("a", Reals, All("b", Reals, All("d", Complexes,
            Equal(Typed(LocalCall("cssShape", F.Id("n"), a, b, d), MatrixType),
                LambdaOf("x", Words, LambdaOf("y", Words, entries)))))));
    }

    private static Formula IsCssShapeFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var d = F.Id("d");
        var restrictions = And(LE(Typed(D(0), Reals), a),
            And(LE(a, Typed(D(1), Reals)), And(LE(Typed(D(0), Reals), b),
                And(LE(b, Typed(D(1), Reals)), And(LE(Add(a, b), Typed(D(1), Reals)),
                    And(LE(new Formula.Norm(d), Divide(a, Typed(D(2), Reals))),
                        Equal(SigmaLower, LocalCall("cssShape", F.Id("n"), a, b, d))))))));
        return All("n", Naturals, All("σ", MatrixType,
            Equal(Typed(LocalCall("IsCssShape", SigmaLower), Qualified("Prop")),
                Parenthesized(Some("a", Reals, Some("b", Reals, Some("d", Complexes, restrictions)))))));
    }

    private static Formula HsSqFormula()
    {
        var difference = Subtract(Rho, SigmaLower);
        var value = At(Qualified("D5", "S3", "Quantum", "Tomography",
            "RankOneContextCommutator", "hilbertSchmidtSquare"), difference);
        return All("n", Naturals, All("ρ", MatrixType, All("σ", MatrixType,
            Equal(Typed(LocalCall("hsSq", Rho, SigmaLower), Reals), value))));
    }

    private static Formula ClaimFormula()
    {
        var rho = LocalCall("xmems", F.Id("n"), GammaLower);
        var minimum = All("τ", MatrixType, Arrow(FullySeparableAt(Tau),
            LE(LocalCall("hsSq", rho, SigmaLower), LocalCall("hsSq", rho, Tau))));
        var attained = Some("σ", MatrixType, And(FullySeparableAt(SigmaLower),
            And(LocalCall("IsCssShape", SigmaLower), minimum)));
        var bound = LE(new Formula.Norm(GammaLower), Divide(Typed(D(1), Reals),
            Add(Pow(Typed(D(2), Reals), Exponent), Typed(D(1), Reals))));
        return Equal(Typed(Local("claim"), Qualified("Prop")), Parenthesized(All("n", Naturals,
            Arrow(LE(Typed(D(2), Naturals), F.Id("n")), All("γ", Complexes, Arrow(bound, attained))))));
    }

    private static Formula FullySeparableAt(Formula matrix) => At(Qualified("D5", "S3", "Quantum",
        "Entanglement", "FullySeparableExchangeObstruction", "IsFullySeparableLocal"), matrix);
    private static Formula FirstBitZero(Formula x) => Some("k", FinOf(F.Id("n")),
        And(Equal(At(Qualified("Fin", "val"), F.Id("k")), Typed(D(0), Naturals)),
            Equal(At(x, F.Id("k")), Typed(D(0), FinOf(D(2))))));
    private static Formula ConstantBit(byte bit) =>
        At(Qualified("Function", "const"), FinOf(F.Id("n")), Typed(D(bit), FinOf(D(2))));
    private static Formula Exponent => Subtract(F.Id("n"), Typed(D(1), Naturals));
    private static Formula Words => Arrow(FinOf(F.Id("n")), FinOf(D(2)));
    private static Formula MatrixType => At(Qualified("Matrix"), Words, Words, Complexes);
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula OfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), condition, yes, no);
    private static Formula LE(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(Variable(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(Variable(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(Variable(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Variable(string name) => name switch
    {
        "γ" => GammaLower,
        "σ" => SigmaLower,
        "ρ" => Rho,
        "τ" => Tau,
        _ => F.Id(name),
    };
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Entanglement",
        "GeometricMeasure", "XMemsClosestSeparableShapeRefutation", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
}
