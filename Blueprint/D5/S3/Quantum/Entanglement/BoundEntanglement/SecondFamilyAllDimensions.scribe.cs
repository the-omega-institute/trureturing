using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.BoundEntanglement;

internal sealed class SecondFamilyAllDimensionsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/paltothbenevertesi2021singlet");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic translations supply the orthogonal matrices, difference labels, and sum-indexed shield vectors required for the second family in every dimension.",
        H("Second-family data in every dimension"),
        Blocks(
            Node("multiplicity", "The nonzero label-fiber multiplicity", MultiplicityFormula(),
                "For a natural dimension d, a real array a on pairs of Fin d and a label array μ on the same pairs, multiplicity a μ m is the finite cardinality of the subtype of pairs p whose value a p.1 p.2 is nonzero and whose label μ p.1 p.2 equals m. This is the number N_m of nonzero pairs in the m-th label fiber. The source introduces these fibers in TeX lines 606–614."),
            Node("tVec", "The label-indexed vector", TVecFormula(),
                "For each label m, tVec a μ m is the complex-valued vector on pairs whose coordinate at p equals a p.1 p.2 divided by the square root of d, with both real quantities coerced to complex numbers, when that coefficient is nonzero and μ p.1 p.2=m; the coordinate is zero otherwise. This is the coordinate form of the vectors t_m in Definition 2, TeX lines 627–631."),
            Describe.Lean(
                DescribeId.Create("second-family-all-dimensions-issecondfamilydata"),
                DeclarationHandle.Create(Prefix + "IsSecondFamilyData"),
                H("The requirements for second-family data"),
                StatementSource.FromAuthor(Disp(IsSecondFamilyDataFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "IsSecondFamilyData d q qbar μ a s collects the formal requirements of Definition 2. Every q j is orthogonal, the rows qbar m are orthonormal, and q k i j equals a i j times qbar (μ i j) k. Every nonzero coefficient has square d divided by the multiplicity of its label fiber. The vectors s m are orthonormal in the complex pair space, and the partial transpose of their projector sum equals the projector sum formed from tVec. These are the orthogonality, factorization, normalization, and shield requirements stated at TeX lines 567–571, 594–640.")),
                    Paragraph(Text("The shield identity uses "),
                        Ref("D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose"),
                        Text(", the second-factor partial transpose: its entry at (p,q) is the input entry at ((p.1,q.2),(q.1,p.2))."))),
                DescribeRole.Definition),
            Node("claim", "Existence of second-family data", ClaimFormula(),
                "The claim asks for second-family data for every natural dimension d at least two, as in the source's question at TeX line 674. Its five witnesses are a family q of d real d-by-d matrices, a family qbar of d real vectors on Fin d, a label function μ on pairs, a real coefficient function a on pairs, and a family s of d complex vectors on pairs. The witnesses satisfy all six requirements of IsSecondFamilyData."),
            Describe.Lean(
                DescribeId.Create("second-family-all-dimensions-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Cyclic translations prove existence in every dimension"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix d at least two. For each k in Fin d, let Qᵏ be the real permutation matrix of the cyclic shift i ↦ i+k on Fin d. "
                            + "The shift is Mathlib's permutation finCycle k; Equiv.Perm.permMatrix_mem_unitaryGroup gives unitarity, and real conjugation turns its adjoint identity into (Qᵏ)ᵀQᵏ=1.")),
                    Paragraph(Text(
                        "Set μ i j to be the cyclic difference j−i in Fin d, set a i j=1, and let qbar m be the m-th coordinate vector. "
                            + "Thus Qᵏ i j is one exactly when j=i+k, equivalently k=μ i j, and the shift factorization says Qᵏ i j = a i j qbar (μ i j) k. The map i ↦ (i,i+m) parametrizes the m-th label fiber bijectively, so its multiplicity is d and the square law for a is d/d=1. "
                            + "The coordinate vectors qbar are orthonormal by a finite case split on their labels.")),
                    Paragraph(Text(
                        "For these witnesses, tVec at label m has coefficient (sqrt d)⁻¹ on pairs with j−i=m and zero elsewhere. All sums and differences of pair coordinates are taken modulo d.")),
                    Paragraph(Text(
                        "Define the shield vector at label m by the constant coefficient (sqrt d)⁻¹ on pairs with i+j=m in the cyclic group and zero elsewhere. "
                            + "Transport (i,j) to the two-coordinate residue string (i,−j) through ZMod.finEquiv d. The shield vector becomes the zero-frequency Fourier vector with sector label (0,−m). The shared sector_basis theorem in AbsolutePPT.Bipartite then proves orthonormality.")),
                    Paragraph(Text(
                        "For the partial-transpose identity, evaluate both matrix sides at arbitrary pair indices p and q. "
                            + "After the pair-coordinate substitution, the shield side is nonzero exactly when q.1+p.2=p.1+q.2, which is equivalent in the cyclic group to q.2−q.1=p.2−p.1. "
                            + "That is exactly equality of the difference labels, so the resulting entry agrees with the sum of the tVec projectors. "
                            + "These constructions give the five witnesses and IsSecondFamilyData, proving the full quantified claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pal-toth-bene-vertesi-2021-second-family-all-dimensions"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("second-family-all-dimensions-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula MultiplicityFormula()
    {
        Formula d = X("d");
        Formula pair = PairType(d);
        Formula p = X("p");
        Formula condition = And(
            Neq(At(X("a"), Fst(p), Snd(p)), Typed(D(0), Reals())),
            Equal(At(X("μ"), Fst(p), Snd(p)), X("m")));
        Formula subtype = At(Qualified("Subtype"), pair, LambdaOf("p", pair, condition));
        Formula body = Equal(
            LocalCall("multiplicity", X("a"), X("μ"), X("m")),
            At(Qualified("Fintype", "card"), subtype));
        return All("d", Naturals(), All("a", Arrow(FinOf(d), Arrow(FinOf(d), Reals())),
            All("μ", Arrow(FinOf(d), Arrow(FinOf(d), FinOf(d))),
                All("m", FinOf(d), body))));
    }

    private static Formula TVecFormula()
    {
        Formula d = X("d");
        Formula p = X("p");
        Formula value = At(X("a"), Fst(p), Snd(p));
        Formula label = At(X("μ"), Fst(p), Snd(p));
        Formula condition = And(Neq(value, Typed(D(0), Reals())), Equal(label, X("m")));
        Formula numerator = Typed(value, Complexes());
        Formula denominator = Typed(
            At(Qualified("Real", "sqrt"), Typed(d, Reals())), Complexes());
        Formula body = Equal(
            At(Local("tVec"), X("a"), X("μ"), X("m"), p),
            If(condition, Div(numerator, denominator), Typed(D(0), Complexes())));
        return All("d", Naturals(),
            All("a", Arrow(FinOf(d), Arrow(FinOf(d), Reals())),
                All("μ", Arrow(FinOf(d), Arrow(FinOf(d), FinOf(d))),
                    All("m", FinOf(d), All("p", PairType(d), body)))));
    }

    private static Formula IsSecondFamilyDataFormula()
    {
        Formula d = X("d");
        Formula q = X("q");
        Formula qbar = X("qbar");
        Formula mu = X("μ");
        Formula a = X("a");
        Formula s = X("s");
        Formula fin = FinOf(d);
        Formula pair = PairType(d);
        Formula realMatrix = MatrixType(fin, Reals());
        Formula qType = Arrow(fin, realMatrix);
        Formula qbarType = Arrow(fin, Arrow(fin, Reals()));
        Formula muType = Arrow(fin, Arrow(fin, fin));
        Formula aType = Arrow(fin, Arrow(fin, Reals()));
        Formula sType = Arrow(fin, Arrow(pair, Complexes()));

        Formula orthogonal = All("j", fin,
            Equal(
                Mul(At(Qualified("Matrix", "transpose"), At(q, X("j"))), At(q, X("j"))),
                Typed(D(1), realMatrix)));
        Formula qbarOrthonormal = All("m", fin, All("n", fin,
            Equal(
                SumOver("k", fin, Mul(At(qbar, X("m"), X("k")), At(qbar, X("n"), X("k")))),
                If(Equal(X("m"), X("n")), Typed(D(1), Reals()), Typed(D(0), Reals())))));
        Formula factorization = All("i", fin, All("j", fin, All("k", fin,
            Equal(
                At(q, X("k"), X("i"), X("j")),
                Mul(At(a, X("i"), X("j")),
                    At(qbar, At(mu, X("i"), X("j")), X("k")))))));
        Formula squareLaw = All("i", fin, All("j", fin,
            Imply(Neq(At(a, X("i"), X("j")), Typed(D(0), Reals())),
                Equal(
                    Pow(At(a, X("i"), X("j")), D(2)),
                    Div(Typed(d, Reals()),
                        Typed(LocalCall("multiplicity", a, mu,
                            At(mu, X("i"), X("j"))), Reals()))))));
        Formula shieldOrthonormal = All("m", fin, All("n", fin,
            Equal(
                SumOver("x", pair, Mul(
                    Call("star", At(s, X("m"), X("x"))),
                    At(s, X("n"), X("x")))),
                If(Equal(X("m"), X("n")), Typed(D(1), Complexes()), Typed(D(0), Complexes())))));
        Formula transposeIdentity = Equal(
            At(Qualified("D5", "S3", "Quantum", "Entanglement", "AbsolutePPT",
                    "Bipartite", "partialTranspose"),
                SumOver("m", fin, Outer(At(s, X("m"))))),
            SumOver("m", fin, Outer(At(Local("tVec"), a, mu, X("m")))));
        Formula body = Conjunction(orthogonal,
            Conjunction(qbarOrthonormal,
                Conjunction(factorization,
                    Conjunction(squareLaw,
                        Conjunction(shieldOrthonormal, transposeIdentity)))));
        return All("d", Naturals(), All("q", qType,
            All("qbar", qbarType, All("μ", muType,
                All("a", aType, All("s", sType,
                    Iff(At(Local("IsSecondFamilyData"), d, q, qbar, mu, a, s), body)))))));
    }

    private static Formula ClaimBody()
    {
        Formula d = X("d");
        Formula fin = FinOf(d);
        Formula qType = Arrow(fin, MatrixType(fin, Reals()));
        Formula qbarType = Arrow(fin, Arrow(fin, Reals()));
        Formula muType = Arrow(fin, Arrow(fin, fin));
        Formula aType = Arrow(fin, Arrow(fin, Reals()));
        Formula sType = Arrow(fin, Arrow(PairType(d), Complexes()));
        Formula data = Ex("q", qType,
            Ex("qbar", qbarType,
                Ex("μ", muType,
                    Ex("a", aType,
                        Ex("s", sType,
                            At(Local("IsSecondFamilyData"), d, X("q"), X("qbar"),
                                X("μ"), X("a"), X("s")))))));
        return All("d", Naturals(),
            Imply(Leq(Typed(D(2), Naturals()), d), data));
    }

    private static Formula ClaimFormula() =>
        Iff(LocalCall("claim"), ClaimBody());

    private static Formula Outer(Formula vector) =>
        At(Qualified("Matrix", "vecMulVec"), vector, Call("star", vector));

    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));

    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));

    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));

    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), Parenthesized(condition), yes, no);

    private static Formula Imply(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula And(Formula left, Formula right) => Conjunction(left, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Neq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);

    private static Formula Fst(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Snd(Formula value) => At(Qualified("Prod", "snd"), value);

    private static Formula PairType(Formula d) =>
        At(Qualified("Prod"), FinOf(d), FinOf(d));

    private static Formula FinOf(Formula d) => At(Qualified("Fin"), d);

    private static Formula MatrixType(Formula index, Formula scalar) =>
        At(Qualified("Matrix"), index, index, scalar);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Entanglement", "BoundEntanglement",
            "SecondFamilyAllDimensions", name);

    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);

    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));

    private static Formula X(string name) => name == "μ" ? Mu : F.Id(name);

    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
