using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class SingleMeasurementPseudobroadcastingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/jokinenetal2024nobroadcasting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One four-outcome qubit POVM generates a contextual subtheory that admits one-copy pseudo-broadcasting.",
        H("One measurement does not force noncontextuality"),
        Blocks(
            DefinitionNode("subtheory", "Subtheory", "Convex quantum subtheories", SubtheoryFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The allowed states t form a convex set of density matrices. The allowed operators a form a convex set of effects: "
                    + "both e and 1 − e are positive semidefinite, the identity belongs to a, and a is closed under complements. "
                    + "This is the subtheory of arXiv:2406.07305v1, Arxiv.tex, line 321. "
                    + "The dimension d is arbitrary, including zero, and no nonemptiness condition is imposed on t."),
            DefinitionNode("postprocessings", "postprocessings", "Binary classical post-processings", PostprocessingsFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For a finite family p of matrices, choose one real coefficient c o in the unit interval for each outcome o, "
                    + "and sum the matrices with these coefficients. Each coefficient is explicitly included in the complex scalars. "
                    + "For a POVM this is one effect of a binary classical post-processing, with the other effect obtained from the coefficients 1 − c o. "
                    + "The source defines classical post-processing in Arxiv.tex, line 275. The definition also applies to families that are not POVMs."),
            DefinitionNode("generated-by", "GeneratedBy", "Generation by k finite POVMs", GeneratedByFormula(),
                AssessedProvenance.FromRepo(Source),
                "For each j in Fin k, choose a natural outcome count m j and a POVM p j. "
                    + "The set a is exactly the real convex hull of the union of their binary classical post-processings. "
                    + "This specifies the meaning of generation used here for the question in Arxiv.tex, lines 348 and 482. "
                    + "The generators need not be independent or distinct, and k need not be positive."),
            DefinitionNode("partial-trace-keep", "partialTraceKeep", "Keeping one tensor coordinate", PartialTraceKeepFormula(),
                AssessedProvenance.FromRepo(Source),
                "A tensor basis label is a function from Fin n to Fin d. Split it into its coordinate at i and its function on the remaining coordinates. "
                    + "Reindex both matrix indices by this splitting and trace out the second factor. "
                    + "In the displayed dependent conditional, the equal branch is constant on proofs of j = i; "
                    + "the unequal branch uses its proof h to form an index of the remaining coordinates."),
            DefinitionNode("pseudo-broadcastable", "PseudoBroadcastable", "Pseudo-broadcasting to n copies", PseudoBroadcastableFormula(),
                AssessedProvenance.FromLiterature(Source),
                "There is a complex linear map ξ into the n-fold tensor matrix space. It preserves the trace of every input matrix, "
                    + "preserves every allowed one-coordinate expectation, and gives nonnegative expectations for every product of allowed effects. "
                    + "Complete positivity is not required. This is the common-effect-set case of Arxiv.tex, lines 328–333. "
                    + "The constant family Function.const takes domain Fin n and value Fin d. "
                    + "All traces and their zero bounds are complex; the order on complex numbers requires a nonnegative real part and zero imaginary part."),
            DefinitionNode("noncontextual", "Noncontextual", "A preparation and measurement noncontextual model", NoncontextualFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Choose any type ι of hidden labels and two matrix families g and s. For every allowed state, its traces against g are nonnegative "
                    + "and sum to one. Each s l has trace one and gives nonnegative responses on the allowed effects. "
                    + "The sum of preparation weight times response reproduces every allowed Born probability. "
                    + "HasSum expresses convergence over arbitrary finite subsets of ι; neither a finite label set nor global positivity of g and s is required. "
                    + "These are the restricted positivity and normalization requirements of Arxiv.tex, lines 321–326."),
            DefinitionNode("claim", "claim", "The equivalence for k generating measurements", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For all natural dimensions d and all natural k, a subtheory generated by k finite POVMs admits k-copy pseudo-broadcasting "
                    + "if and only if it has a preparation and measurement noncontextual model. "
                    + "The source asks for this equivalence in Arxiv.tex, lines 348 and 482. The displayed statement uses the precise generation condition above "
                    + "and includes k = 0; its failure will occur at the positive value k = 1."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A qubit counterexample at k equal to one"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take four complex column vectors v₀ = (3,1), v₁ = (1,3), v₂ = (3,−1), v₃ = (1,−3), "
                            + "and the states ρⱼ = vⱼvⱼ*/10. Take four vectors w₀ = (1,1), w₁ = (1,−1), w₂ = (1,0), w₃ = (0,1), "
                            + "and operators M₀ = w₀w₀*/4, M₁ = w₁w₁*/4, M₂ = w₂w₂*/2, M₃ = w₃w₃*/2. "
                            + "Outer-product positivity and the squared norms of the vⱼ show that each ρⱼ is a density matrix. "
                            + "The Mₒ are positive semidefinite and their sum is the identity, so they form a POVM.")),
                    Paragraph(Text(
                        "The binary post-processings of any finite matrix family form the linear image of a real unit cube and are therefore convex. "
                            + "For a POVM, replacing each coefficient c o by 1 − c o gives the complement of the corresponding effect. "
                            + "Nonnegative coefficients give positive semidefinite operators. Each Mₒ belongs to this set by choosing its coordinate indicator. "
                            + "Let T be the convex hull of the four ρⱼ and A the convex hull of the post-processings of M. "
                            + "Convexity makes A equal to the post-processing set itself. Convexity of the density matrices gives the state condition for T; "
                            + "positivity of an effect and its complement gives the effect condition for A. Choosing every coefficient equal to one gives the identity. "
                            + "Thus T and A form a subtheory, and the single generator M proves GeneratedBy A 1.")),
                    Paragraph(Text(
                        "Every subtheory admits one-copy pseudo-broadcasting. Identify the functions Fin 1 → Fin d with Fin d by evaluation at the unique coordinate, "
                            + "and let ξ be the induced complex linear reindexing of matrices. Reindexing preserves the trace. "
                            + "For the one-coordinate partial trace, the type of remaining coordinates is empty, so its function space has one element; "
                            + "the partial trace is consequently the original matrix. A product over Fin 1 is its sole factor. "
                            + "The remaining nonnegativity condition follows from the nonnegative trace of the product of a density matrix and a positive semidefinite effect.")),
                    Paragraph(Text(
                        "For the numerical bound, let u,v,w,z be nonnegative real numbers with u + z = v + w, and let 0 ≤ x,y ≤ 1/2. "
                            + "Then [u(x+y) + v(x+1/2−y) + w(1/2−x+y) + z(1−x−y)]/4 ≤ 3(u+z)/8. "
                            + "To prove it, split according to the signs of u + v − w − z and u + w − v − z. "
                            + "In each of the four cases the bounds on x and y bound their respective affine contributions; the relation u + z = v + w gives the stated right side.")),
                    Paragraph(Text(
                        "Direct matrix arithmetic gives ρ₀ + ρ₃ = ρ₁ + ρ₂ = 1 and M₀ + M₁ = M₂ + M₃ = 1/2 times the identity. "
                            + "Let ix = (0,0,1,1) and iz = (2,3,2,3), indexed by Fin 4. "
                            + "For every j, the two Born probabilities have sum tr(ρⱼ Mᵢₓⱼ) + tr(ρⱼ Mᵢ𝓏ⱼ) = 17/20.")),
                    Paragraph(Text(
                        "Suppose a noncontextual model with label type ι and families g,s exists. Set μ j l = tr(ρⱼ g l) and r o l = tr(s l Mₒ). "
                            + "All four states and all four operators are allowed. Hence the μ and r are nonnegative complex numbers, "
                            + "each family μ j has sum one, and the products μ j l · r o l sum to tr(ρⱼ Mₒ). "
                            + "Linearity and the two state decompositions give μ 0 l + μ 3 l = μ 1 l + μ 2 l. "
                            + "Linearity, the two effect decompositions and tr(s l) = 1 give r 0 l + r 1 l = r 2 l + r 3 l = 1/2.")),
                    Paragraph(Text(
                        "Apply the affine bound with u,v,w,z the real parts of μ 0 l, μ 1 l, μ 2 l, μ 3 l, and x,y the real parts of r 0 l,r 2 l. "
                            + "Nonnegativity supplies zero imaginary parts for the μ, and the response sums put x,y in the required half-interval. "
                            + "It follows pointwise that one quarter of the sum over j of Re[μ j l · (r (ix j) l + r (iz j) l)] "
                            + "is at most (3/8)·[Re(μ 0 l) + Re(μ 3 l)]. "
                            + "The latter two real weight families together have sum 2. For each j, adding the two reproduction identities and taking real parts "
                            + "shows that the corresponding score family has sum 17/20. Summing the four score families and dividing by four keeps this sum equal to 17/20. "
                            + "Monotonicity of these convergent sums would therefore give 17/20 ≤ (3/8)·2 = 3/4, a contradiction.")),
                    Paragraph(Text(
                        "Finally, apply the asserted equivalence with d = 2, k = 1, t = T and a = A. "
                            + "The subtheory and single-generator properties supply its hypotheses, and the one-copy map supplies its pseudo-broadcasting side. "
                            + "Its noncontextual side contradicts the bound just proved. Thus the equivalence fails already for one finite qubit POVM."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jokinen-et-al-2024-k-measurement-pseudobroadcasting"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock DefinitionNode(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula SubtheoryFormula()
    {
        Formula states = All("ρ", Mat(), Imp(Member(X("ρ"), X("t")),
            At(Qualified("D5", "S3", "QuantumChannels", "CoPRelativeQuantumnessRefutation", "IsDensity"), X("ρ"))));
        Formula positive = All("e", Mat(), Imp(Member(X("e"), X("a")),
            And(Positive(X("e")), Positive(Sub(Typed(D(1), Mat()), X("e"))))));
        Formula complements = All("e", Mat(), Imp(Member(X("e"), X("a")),
            Member(Sub(Typed(D(1), Mat()), X("e")), X("a"))));
        Formula body = And(At(Qualified("Convex"), Reals(), X("t")),
            And(states, And(At(Qualified("Convex"), Reals(), X("a")),
                And(positive, And(Member(Typed(D(1), Mat()), X("a")), complements)))));
        return StateEffectBinders(IffOf(LocalCall("Subtheory", X("t"), X("a")), body));
    }

    private static Formula PostprocessingsFormula()
    {
        Formula coefficients = All("o", FinOf(X("m")),
            And(LE(Typed(D(0), Reals()), At(X("c"), X("o"))),
                LE(At(X("c"), X("o")), Typed(D(1), Reals()))));
        Formula sum = SumOver("o", FinOf(X("m")),
            Smul(At(Qualified("Complex", "ofReal"), At(X("c"), X("o"))), At(X("p"), X("o"))));
        Formula set = SetOf("e", Mat(), Some("c", Arrow(FinOf(X("m")), Reals()),
            And(coefficients, Equal(X("e"), sum))));
        return All("d", Naturals(), All("m", Naturals(), All("p", Arrow(FinOf(X("m")), Mat()),
            Equal(LocalCall("postprocessings", X("p")), set))));
    }

    private static Formula GeneratedByFormula()
    {
        Formula familyType = DependentArrow("j", FinOf(X("k")), Arrow(FinOf(At(X("m"), X("j"))), Mat()));
        Formula union = Seq(new Formula.Subscript(Cup, Seq(X("j"), Colon, Sp, FinOf(X("k")))), Sp,
            Parenthesized(LocalCall("postprocessings", At(X("p"), X("j")))));
        Formula body = Some("m", Arrow(FinOf(X("k")), Naturals()), Some("p", familyType,
            And(All("j", FinOf(X("k")),
                    At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "ConcealmentKernelNecessityRefutation", "IsPOVM"),
                        At(X("p"), X("j")))),
                Equal(X("a"), At(Qualified("convexHull"), Reals(), union)))));
        return All("d", Naturals(), All("a", SetType(Mat()), All("k", Naturals(),
            IffOf(LocalCall("GeneratedBy", X("a"), X("k")), body))));
    }

    private static Formula PartialTraceKeepFormula()
    {
        Formula other = At(Qualified("Subtype"), LambdaOf("j", FinOf(X("n")), NotEqual(X("j"), X("i"))));
        Formula splitType = At(Qualified("Prod"), FinOf(X("d")), Arrow(other, FinOf(X("d"))));
        Formula condition = Equal(X("j"), X("i"));
        Formula coordinate = At(Qualified("dite"), condition,
            At(Qualified("Function", "const"), condition, At(Qualified("Prod", "fst"), X("z"))),
            LambdaOf("h", new Formula.Not(Parenthesized(condition)),
                At(At(Qualified("Prod", "snd"), X("z")), At(Qualified("Subtype", "mk"), X("j"), X("h")))));
        Formula splitting = LambdaOf("z", splitType, LambdaOf("j", FinOf(X("n")), coordinate));
        Formula body = At(Qualified("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", "partialTraceRight"),
            At(Qualified("Matrix", "submatrix"), X("x"), splitting, splitting));
        return All("d", Naturals(), All("n", Naturals(), All("i", FinOf(X("n")), All("x", TensorMat(),
            Equal(Typed(LocalCall("partialTraceKeep", X("i"), X("x")), Mat()), body)))));
    }

    private static Formula PseudoBroadcastableFormula()
    {
        Formula trace = All("x", Mat(), Equal(Trace(At(X("ξ"), X("x"))), Trace(X("x"))));
        Formula marginals = All("i", FinOf(X("n")), All("ρ", Mat(), Imp(Member(X("ρ"), X("t")),
            All("e", Mat(), Imp(Member(X("e"), X("a")),
                Equal(Trace(Mul(X("e"), LocalCall("partialTraceKeep", X("i"), At(X("ξ"), X("ρ"))))),
                    Trace(Mul(X("e"), X("ρ")))))))));
        Formula product = At(Qualified("D5", "S3", "Quantum", "Recovery", "ProductPrefixRigidity", "productMap"),
            At(Qualified("Function", "const"), FinOf(X("n")), FinOf(X("d"))), X("e"));
        Formula nonnegative = All("ρ", Mat(), Imp(Member(X("ρ"), X("t")),
            All("e", Arrow(FinOf(X("n")), Mat()),
                Imp(All("i", FinOf(X("n")), Member(At(X("e"), X("i")), X("a"))),
                    LE(Typed(D(0), Complexes()), Trace(Mul(At(X("ξ"), X("ρ")), product)))))));
        Formula mapType = At(Qualified("LinearMap"), Complexes(), Mat(), TensorMat());
        return StateEffectBinders(All("n", Naturals(), IffOf(LocalCall("PseudoBroadcastable", X("t"), X("a"), X("n")),
            Some("ξ", mapType, And(trace, And(marginals, nonnegative))))));
    }

    private static Formula NoncontextualFormula()
    {
        Formula weights = All("l", X("ι"), All("ρ", Mat(), Imp(Member(X("ρ"), X("t")),
            LE(Typed(D(0), Complexes()), Trace(Mul(X("ρ"), At(X("g"), X("l"))))))));
        Formula mass = All("ρ", Mat(), Imp(Member(X("ρ"), X("t")),
            At(Qualified("HasSum"), LambdaOf("l", X("ι"), Trace(Mul(X("ρ"), At(X("g"), X("l"))))),
                Typed(D(1), Complexes()))));
        Formula responses = All("l", X("ι"), All("e", Mat(), Imp(Member(X("e"), X("a")),
            LE(Typed(D(0), Complexes()), Trace(Mul(At(X("s"), X("l")), X("e")))))));
        Formula normalization = All("l", X("ι"), Equal(Trace(At(X("s"), X("l"))), Typed(D(1), Complexes())));
        Formula reproduce = All("ρ", Mat(), Imp(Member(X("ρ"), X("t")), All("e", Mat(), Imp(Member(X("e"), X("a")),
            At(Qualified("HasSum"), LambdaOf("l", X("ι"),
                    Mul(Trace(Mul(X("ρ"), At(X("g"), X("l")))), Trace(Mul(At(X("s"), X("l")), X("e"))))),
                Trace(Mul(X("ρ"), X("e"))))))));
        Formula model = Some("ι", Qualified("Type"), Some("g", Arrow(X("ι"), Mat()), Some("s", Arrow(X("ι"), Mat()),
            And(weights, And(mass, And(responses, And(normalization, reproduce)))))));
        return StateEffectBinders(IffOf(LocalCall("Noncontextual", X("t"), X("a")), model));
    }

    private static Formula ClaimFormula()
    {
        Formula body = All("d", Naturals(), All("k", Naturals(), All("t", SetType(Mat()), All("a", SetType(Mat()),
            Imp(LocalCall("Subtheory", X("t"), X("a")), Imp(LocalCall("GeneratedBy", X("a"), X("k")),
                IffOf(LocalCall("PseudoBroadcastable", X("t"), X("a"), X("k")),
                    LocalCall("Noncontextual", X("t"), X("a")))))))));
        return IffOf(Local("claim"), body);
    }

    private static Formula X(string name) => name switch
    {
        "ρ" => Rho,
        "ξ" => Xi,
        "ι" => Iota,
        _ => F.Id(name),
    };
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
    private static Formula Local(string name) => Qualified("D5", "S3", "QuantumContext", "SingleMeasurementPseudobroadcastingRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Mat() => At(Qualified("Matrix"), FinOf(X("d")), FinOf(X("d")), Complexes());
    private static Formula TensorMat() => At(Qualified("Matrix"), Arrow(FinOf(X("n")), FinOf(X("d"))),
        Arrow(FinOf(X("n")), FinOf(X("d"))), Complexes());
    private static Formula SetType(Formula type) => At(Qualified("Set"), type);
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, X(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula DependentArrow(string name, Formula type, Formula body) =>
        Seq(Typed(X(name), type), Sp, To, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Imp(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(Parenthesized(hypothesis), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Trace(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula Positive(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula StateEffectBinders(Formula body) => All("d", Naturals(),
        All("t", SetType(Mat()), All("a", SetType(Mat()), body)));
}
