using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ObliqueDiscordMutualInformationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/xu2015oblique");
    private const string BasisQuote = "Suppose $\\{|i\\rangle \\}_{i=1}^{n_{A}}$ is a normalized basis of $H^{A}$ which not necessarily orthogonal to each other. There exists an unique basis $\\{|\\widetilde{i}\\rangle \\}_{i=1}^{n}$ of $H^{A}$ such that $\\langle i|\\widetilde{j}\\rangle =\\delta _{ij}$, note that $\\{|\\widetilde{i}\\rangle \\}_{i=1}^{n}$ not necessarily orthogonal and not necessarily normalized. $\\{|\\widetilde{i}\\rangle \\}_{i=1}^{n_{A}}$ is called the dual basis of $\\{|i\\rangle \\}_{i=1}^{n_{A}}$.";
    private const string OperationQuote = "We define the quantum operation $\\Phi _{A}=\\{|i\\rangle \\langle \\widetilde{i}|\\}_{i=1}^{n_{A}}$ which operates the bipartite state $\\rho ^{AB}$ as $\\Phi _{A}\\rho ^{AB}=\\frac{\\sum_{i=1}^{n_{A}}|i\\rangle \\langle \\widetilde{i}|\\rho ^{AB}|\\widetilde{i}\\rangle \\langle i|}{tr[\\sum_{i=1}^{n_{A}}\\langle \\widetilde{i}|\\rho ^{AB}|\\widetilde{i}\\rangle ]}$.";
    private const string ConjectureQuote = "Conjecture: $I(\\rho ^{AB})\\geq I(\\Phi _{A}\\rho ^{AB})$ for any $\\Phi _{A}$ and any $\\rho ^{AB}$, where $I(\\rho ^{AB})$ is the mutual information, $\\Phi _{A}$ is defined in Eq.(13).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized oblique operation can increase two-qubit mutual information. The state (8|00> + |11>)/sqrt(65) and the normalized oblique basis (2, +/-1)/sqrt(5) refute Xu's Conjecture, Eq. (22) of arXiv:1506.00404v1.",
        H("Oblique discord: mutual information can increase"),
        Blocks(
            Node("ObliqueBasis", "Normalized basis and biorthogonal dual", BasisFormula(),
                "Xu, p. 2 immediately before Eq. (13): \"" + BasisQuote + "\" The structure has two actual Module.Basis objects v and w, followed by the normalized and dual proof fields displayed below. Fin n indexes the source's n vectors from zero. The inner product conjugates its first argument. KroneckerDelta(i,j) is 1 if i = j and 0 otherwise.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("kraus", "Oblique Kraus matrices", KrausFormula(),
                "The i-th matrix is |v_i><w_i|. vecMulVec forms the outer product and star conjugates each vector entry. Each matrix acts on the A factor.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rawOblique", "Unnormalized bipartite operation", RawFormula(),
                "Tensor each oblique Kraus matrix with the identity matrix on B, then sum K rho K^H. Matrix.kronecker is the matrix Kronecker product; the typed 1 is the identity on Fin nB, and conjTranspose denotes conjugate transpose. The input of rawOblique is a matrix rather than a density-state subtype.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("normalizer", "Source denominator", NormalizerFormula(),
                "The rectangular matrix L_i is the bra w_i tensor the identity on B, so L_i rho L_i^H is the B-valued sandwich <w_i|rho|w_i>. partialTraceRight takes the trace over B and leaves a one-dimensional Unit factor; evaluating at ((),()) extracts the scalar. normalizer is its real part. The source denominator is therefore the trace over B of the sum of these sandwiches.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phi", "State-dependent source normalization", PhiFormula(),
                "Xu, p. 2, Eq. (13): \"" + OperationQuote + "\" phi divides by normalizer, the partial trace over B of the sum of dual-vector sandwiches printed in Eq. (13). Unit norm of each v_i implies that this scalar equals the real trace of the numerator; this equality is proved inside the definition. The displayed equality describes its underlying value; its positivity and trace-one proofs package it as a DensityState. CStarMatrix.ofMatrix embeds the matrix and SMul.smul applies its real scalar. The binder ht is the proof of a strictly positive normalizing trace.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Xu's conjectured monotonicity", ClaimFormula(),
                "Xu, p. 3, Eq. (22): \"" + ConjectureQuote + "\" Its operation on p. 2, Eq. (13), is: \"" + OperationQuote + "\" The quantifiers range over all finite dimensions, all normalized oblique bases with their duals, and all bipartite density states for which the operation is defined. DensityState is the positive trace-one CStarMatrix subtype; no entropy value or spectrum is assumed. quantumMutualInformation is the existing sum of the actual marginal vonNeumannEntropy values minus the joint vonNeumannEntropy. The claim uses natural logarithms, which preserve the conjecture's comparison in base two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Two qubits refute monotonicity", Disp(new Formula.Not(F.Id("claim"))),
                "Take v_+ = (2,1)/sqrt(5), v_- = (2,-1)/sqrt(5) and w_+ = (sqrt(5)/4,sqrt(5)/2), w_- = (sqrt(5)/4,-sqrt(5)/2). The input rho is the rank-one projector onto (8|00> + |11>)/sqrt(65). The source normalizer and unnormalized trace are 17/26 and the output tau is (1/85)[[64,0,0,8],[0,4,8,0],[0,8,16,0],[8,0,0,1]]. Rational similarity certificates identify the spectra: rho has eigenvalues 1,0,0,0 and tau has 13/17,4/17,0,0. The marginals of rho are diag(64/65,1/65); those of tau are diag(4/5,1/5) and diag(16/17,1/17). For h(p) = -p log(p) -(1-p) log(1-p), the information gain is h(1/5)+h(1/17)-h(4/17)-2h(1/65) = (7648/1105) log(2) -log(5) -(21/17) log(13) > 0. The elementary comparisons 5^3 < 2^7 and 13^17 < 2^63 certify strict positivity by logarithmic monotonicity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("xu-2015-oblique-discord-mutual-information-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("oblique-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(QuotedProse(prose))), role, resolution);

    private static Inline[] QuotedProse(string prose) => prose.Split('$')
        .SelectMany((part, index) => index % 2 == 0 ? new[] { Text(part) } : SourceInlines(part))
        .ToArray();

    private static Inline[] SourceInlines(string source)
    {
        const string phiA = "Φ<sub><i>A</i></sub>";
        const string rhoAB = "<i>ρ</i><sup><i>AB</i></sup>";
        Formula i = F.Id("i"), ti = Seq(Widetilde, Grp(i));
        Formula nA = new Formula.Subscript(F.Id("n"), F.Id("A"));
        Formula rho = new Formula.Power(Rho, F.Id("AB"));
        return source switch
        {
            "\\Phi _{A}" => [Text(phiA)],
            "\\Phi _{A}=\\{|i\\rangle \\langle \\widetilde{i}|\\}_{i=1}^{n_{A}}" =>
                [Text(phiA + " = "), Math(SourceFamily(Seq(Ket(i), Bra(ti)), nA))],
            "I(\\rho ^{AB})\\geq I(\\Phi _{A}\\rho ^{AB})" =>
                [Math(new Formula.Apply(F.Id("I"), [rho])),
                    Text(" ≥ <i>I</i>(" + phiA + rhoAB + ")")],
            "\\Phi _{A}\\rho ^{AB}=\\frac{\\sum_{i=1}^{n_{A}}|i\\rangle \\langle \\widetilde{i}|\\rho ^{AB}|\\widetilde{i}\\rangle \\langle i|}{tr[\\sum_{i=1}^{n_{A}}\\langle \\widetilde{i}|\\rho ^{AB}|\\widetilde{i}\\rangle ]}" =>
                [Text(phiA + rhoAB + " = "), Math(new Formula.Fraction(
                    SourceSum(Seq(Ket(i), Bra(ti), rho, Ket(ti), Bra(i)), nA),
                    Seq(F.Id("tr"), OpenBracket,
                        SourceSum(Seq(Bra(ti), rho, Ket(ti)), nA), CloseBracket)))],
            _ => [Math(SourceFormula(source))],
        };
    }

    private static Formula SourceFormula(string source)
    {
        Formula i = F.Id("i"), j = F.Id("j"), n = F.Id("n");
        Formula nA = new Formula.Subscript(n, F.Id("A"));
        Formula ti = Seq(Widetilde, Grp(i)), tj = Seq(Widetilde, Grp(j));
        Formula rhoAB = new Formula.Power(Rho, F.Id("AB"));
        return source switch
        {
            "\\{|i\\rangle \\}_{i=1}^{n_{A}}" => SourceFamily(Ket(i), nA),
            "H^{A}" => new Formula.Power(F.Id("H"), F.Id("A")),
            "\\{|\\widetilde{i}\\rangle \\}_{i=1}^{n}" => SourceFamily(Ket(ti), n),
            "\\{|\\widetilde{i}\\rangle \\}_{i=1}^{n_{A}}" => SourceFamily(Ket(ti), nA),
            "\\langle i|\\widetilde{j}\\rangle =\\delta _{ij}" => EqTo(
                Seq(Langle, Sp, i, Bar, tj, Rangle), new Formula.Subscript(DeltaLower, Seq(i, j))),
            "\\rho ^{AB}" => rhoAB,
            "I(\\rho ^{AB})" => new Formula.Apply(F.Id("I"), [rhoAB]),
            "I(\\rho )=S(\\rho ^{A})+S(\\rho ^{B})-S(\\rho )" => EqTo(
                new Formula.Apply(F.Id("I"), [Rho]), Sub(Add(
                    new Formula.Apply(F.Id("S"), [new Formula.Power(Rho, F.Id("A"))]),
                    new Formula.Apply(F.Id("S"), [new Formula.Power(Rho, F.Id("B"))])),
                    new Formula.Apply(F.Id("S"), [Rho]))),
            _ => throw new ArgumentException("Unrecognized source quotation formula.", nameof(source)),
        };
    }

    private static Formula Ket(Formula index) => Seq(Bar, index, Rangle, Sp);
    private static Formula Bra(Formula index) => Seq(Langle, Sp, index, Bar);
    private static Formula SourceFamily(Formula vector, Formula upper) => Seq(
        new Formula.Subscript(Seq(OpenBrace, vector, CloseBrace), EqTo(F.Id("i"), D(1))), Caret, Grp(upper));
    private static Formula SourceSum(Formula body, Formula upper) => Seq(
        new Formula.Subscript(Sum, EqTo(F.Id("i"), D(1))), Caret, Grp(upper), Sp, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(name.Split('.')
            .SelectMany((part, index) => index == 0 ? new[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) })
            .ToArray())), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula EqTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LeTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula LtTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula IffTo(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula States(Formula n) => Call("DensityState", n);
    private static Formula Basis(Formula n) => new Formula.Apply(Seq(Operatorname, Grp(F.Id("Module"), Dot, F.Id("Basis"))), [FinOf(n), Complexes(), Seq(FinOf(n), To, Complexes())]);
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Times, Sp, b));
    private static Formula Joint(Formula a, Formula b) => Product(FinOf(a), FinOf(b));
    private static Formula MatrixOf(Formula rho) => new Formula.Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"), Dot, F.Id("symm"))), [Call("val", rho)]);
    private static Formula At(Formula f, Formula i) => new Formula.Apply(f, [i]);
    private static Formula Inner(Formula x, Formula y) => Call("dotProduct", Call("star", x), y);
    private static Formula SumOf(Formula i, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(i, InMacro, Sp, domain)), Sp, body);
    private static Formula OB(Formula n) => Call("ObliqueBasis", n);
    private static Formula Raw(Formula b, Formula rho) => Call("rawOblique", b, rho);
    private static Formula Normalizer(Formula b, Formula rho) => Call("normalizer", b, MatrixOf(rho));

    private static Formula BasisFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j");
        Formula normalized = All(i, FinOf(n), EqTo(Inner(At(v,i),At(v,i)),D(1)));
        Formula dual = All(i, FinOf(n), All(j, FinOf(n),
            EqTo(Inner(At(v,i),At(w,j)),Call("KroneckerDelta",i,j))));
        Formula fields = Seq(OpenBrace, Sp, v, Colon, Basis(n), Semi, Sp, w, Colon, Basis(n),
            Semi, Sp, F.Id("normalized"), Colon, Parenthesized(normalized), Semi, Sp,
            F.Id("dual"), Colon, Parenthesized(dual), Sp, CloseBrace);
        return Disp(All(n,Nats(),EqTo(OB(n),fields)));
    }

    private static Formula KrausFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), i = F.Id("i");
        return Disp(All(n,Nats(),All(b,OB(n),All(i,FinOf(n),
            EqTo(Call("kraus",b,i),Call("vecMulVec",At(Call("v",b),i),Call("star",At(Call("w",b),i))))))));
    }

    private static Formula RawFormula()
    {
        Formula a = F.Id("nA"), c = F.Id("nB"), b = F.Id("b"), rho = Rho, i = F.Id("i");
        Formula k = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("kronecker"))), [Call("kraus",b,i), Parenthesized(Seq(D(1), Colon, Call("Matrix", FinOf(c), FinOf(c), Complexes())))]);
        Formula value = SumOf(i,FinOf(a),Mul(Mul(k,rho),Call("conjTranspose",k)));
        Formula equation = EqTo(Raw(b,rho),value);
        Formula input = Call("Matrix",Joint(a,c),Joint(a,c),Complexes());
        return Disp(All(a,Nats(),All(c,Nats(),All(b,OB(a),All(rho,input,equation)))));
    }

    private static Formula NormalizerFormula()
    {
        Formula a = F.Id("nA"), c = F.Id("nB"), b = F.Id("b"), rho = Rho;
        Formula i = F.Id("i");
        Formula row = Call("Matrix.replicateRow",F.Id("Unit"),Call("star",At(Call("w",b),i)));
        Formula identity = Parenthesized(Seq(D(1), Colon, Call("Matrix",FinOf(c),FinOf(c),Complexes())));
        Formula l = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("kronecker"))),
            [Parenthesized(row), identity]);
        Formula sandwich = SumOf(i,FinOf(a),Mul(Mul(l,rho),Call("conjTranspose",l)));
        Formula scalar = At(At(Call("partialTraceRight",sandwich),Call("Unit.unit")),Call("Unit.unit"));
        Formula input = Call("Matrix",Joint(a,c),Joint(a,c),Complexes());
        return Disp(All(a,Nats(),All(c,Nats(),All(b,OB(a),All(rho,input,
            EqTo(Call("normalizer",b,rho),Call("Re",scalar)))))));
    }

    private static Formula PhiFormula()
    {
        Formula a = F.Id("nA"), c = F.Id("nB"), b = F.Id("b"), rho = Rho, ht = F.Id("ht");
        Formula t = Raw(b,MatrixOf(rho));
        Formula normalized = new Formula.Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"))), [new Formula.Apply(Seq(Operatorname, Grp(F.Id("SMul"), Dot, F.Id("smul"))), [Call("inv",Normalizer(b,rho)),t])]);
        return Disp(All(a,Nats(),All(c,Nats(),All(b,OB(a),All(rho,States(Joint(a,c)),
            All(ht,LtTo(D(0),Normalizer(b,rho)),EqTo(Call("val",Call("phi",b,rho,ht)),normalized)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula a = F.Id("nA"), c = F.Id("nB"), b = F.Id("b"), rho = Rho, ht = F.Id("ht");
        return Disp(IffTo(F.Id("claim"),All(a,Nats(),All(c,Nats(),All(b,OB(a),
            All(rho,States(Joint(a,c)),All(ht,LtTo(D(0),Normalizer(b,rho)),
                LeTo(Call("quantumMutualInformation",Call("phi",b,rho,ht)),Call("quantumMutualInformation",rho)))))))));
    }
}
