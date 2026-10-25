using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class LocalityTensorProductRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/clavieretal2022localitytensor");
    private static readonly LibraryNoteRef QuotientSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/clavier2025localityhdr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A locality structure on real five-space refutes both conjectures for componentwise and four-way locality.",
        H("Locality tensor products need not be locality vector spaces"),
        Blocks(
            Definition("locality-vector-space", "IsLocalityVectorSpace", "Locality vector spaces",
                LocalityVectorSpaceFormula(),
                "A relation on a K-vector space is a locality vector-space relation when it is symmetric, "
                    + "relates zero to zero, and every polar set is the underlying set of a linear subspace. "
                    + "The polar of U consists of all x related to every u in U. "
                    + "This is Definition 1.1 of arXiv:2205.14616v1, Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 340–359. "
                    + "SetLike.coe explicitly converts the submodule S to its underlying set.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("locality-product", "localityProduct", "The locality Cartesian product",
                LocalityProductFormula(),
                "For subspaces V and W of E, retain exactly the pairs with first component in V, "
                    + "second component in W, and related components. "
                    + "This is the locality Cartesian product of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 387–394.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("span-relation", "spanRel", "The relation on a free span",
                SpanRelationFormula(),
                "Two finitely supported coefficient functions are related when every element of the first support "
                    + "is related to every element of the second support. Empty supports impose no condition. "
                    + "The support formulation of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 755–769, needs only a zero coefficient, "
                    + "so the definition allows an arbitrary type K with Zero K and an arbitrary relation s.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("bilinear-relations", "bilRelations", "The bilinearity submodule",
                BilinearRelationsFormula(),
                "In the free K-vector space on all pairs from E, take the span of the two additivity relations "
                    + "and the two scalar relations, with a and b in V and x and y in W. "
                    + "Finsupp.single assigns the coefficient one in K to the indicated pair. "
                    + "The generators are exactly those of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 422–430; they need not themselves have local support.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("free-span", "freeSpan", "The free span of local pairs",
                FreeSpanFormula(),
                "This submodule consists of the finitely supported functions whose support lies in the locality Cartesian product. "
                    + "It realizes the free span K(V ×_⊤ W) used in the locality tensor product, "
                    + "Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 556–562, inside the free span on all pairs from E.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("bilinear-ideal", "bilIdeal", "Bilinearity relations with local support",
                BilinearIdealFormula(),
                "Intersect the ambient bilinearity submodule with the free span of local pairs. "
                    + "Thus an element must both be a linear combination of bilinearity relations and have local support; "
                    + "the individual relations in that combination need not have local support. "
                    + "This is the subspace I_bil intersected with K(V ×_⊤ W) in Clavier_Foissy_Lopez_Paycha_arxiv.tex, "
                    + "lines 1984–1987, used as the denominator in lines 556–562. Min.min denotes the meet of submodules.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("locality-tensor", "localityTensor", "The locality tensor product",
                LocalityTensorFormula(),
                "The locality tensor product is the free span of local pairs modulo its bilinearity subspace, "
                    + "as in the definition in Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 556–562. "
                    + "CoeSort.coe explicitly regards the free-span submodule as a type of elements. "
                    + "Taking the inverse image under Submodule.subtype puts the denominator inside that type before forming the quotient.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("four-way", "fourWay", "Pairwise locality of four entries",
                FourWayFormula(),
                "The four entries p₁, p₂, q₁ and q₂ must be pairwise related: all six unordered pairs satisfy r. "
                    + "The pairs within each generator are included. This is the literal four-entry condition of "
                    + "arXiv:2506.09493v1, LOC.tex, lines 220 and 743–747. "
                    + "It implies the relational product Prod.RProd r r, namely r(v,v′) ∧ r(w,w′). "
                    + "This componentwise reading is the relation of arXiv:2205.14616v1, Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 447–449. "
                    + "The two relations need not coincide even when V = W.",
                AssessedProvenance.FromLiterature(QuotientSource)),
            Definition("quotient-relation", "quotientRel", "Existential locality on the quotient",
                QuotientRelationFormula(),
                "For a generator relation s, two quotient classes are related if they have representatives "
                    + "whose supports are related by s. Subtype.val explicitly takes each representative to its ambient coefficient function. "
                    + "Relation.Map takes the direct image under the two quotient maps; it requires the existence of related representatives, "
                    + "as in arXiv:2506.09493v1, LOC.tex, lines 606–612. "
                    + "The componentwise and four-way generator relations give the two readings considered here.",
                AssessedProvenance.FromLiterature(QuotientSource)),
            Definition("locality-compatible", "LocalityCompatible", "Locality-compatible subspaces",
                LocalityCompatibleFormula(),
                "A subspace W is locality compatible when the following simultaneous adjustment is possible. "
                    + "If x is related to y and x + w is related to z for some w in W, "
                    + "then a single adjustment w′ in W makes x + w′ related to both y and z. "
                    + "This is Definition 6.7 of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 1880–1886. The predicate itself is defined for any relation r.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("tensor-conjecture", "TensorConjecture", "The locality tensor-product conjecture",
                TensorConjectureFormula(),
                "For a chosen generator-relation rule s, every field K of characteristic zero and K-vector space E, "
                    + "every locality relation r and every pair of subspaces V and W, "
                    + "the conjecture asserts that the quotient locality on the locality tensor product is a locality vector-space relation. "
                    + "This is Conjecture conj:loc_tensor of arXiv:2506.09493v1, LOC.tex, lines 1797–1799. "
                    + "The thesis states no characteristic restriction. Here K has characteristic zero, as in the paper's Notations, "
                    + "Clavier_Foissy_Lopez_Paycha_arxiv.tex, line 321. Refuting this restricted assertion also refutes the unrestricted thesis assertion. "
                    + "Its literal thesis reading uses fourWay; the componentwise reading uses the relation of source 1. "
                    + "K and E range over Type, without a finite-dimensionality hypothesis.",
                AssessedProvenance.FromLiterature(QuotientSource)),
            Definition("pair-conjecture", "PairConjecture", "The locality-compatibility conjecture",
                PairConjectureFormula(),
                "For the same fields K of characteristic zero, vector spaces and subspaces, the conjecture asserts that "
                    + "the bilinearity subspace inside the free span of local pairs is locality compatible "
                    + "with the support relation induced by the chosen generator-relation rule s. "
                    + "Conjectural statement 6.16 of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 1984–1987, uses componentwise locality. "
                    + "Its characteristic-zero restriction is specified in the paper's Notations, line 321. "
                    + "The four-way variant uses the thesis relation on the same generators.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("claim", "claim", "The disjunction of all four assertions",
                ClaimFormula(),
                "The proposition asserts that at least one of the tensor-product or locality-compatibility conjectures "
                    + "holds under either componentwise or four-way locality. Its negation refutes all four assertions separately.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A counterexample to both conjectures under both relations"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Proof(),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("clavier-foissy-lopez-paycha-2022-locality-tensor-product-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static BlockSequence Proof() => Blocks(
        Paragraph(Text(
            "Take K = ℝ, E = ℝ⁵ with coordinates indexed by Fin 5, and V = W = E. "
                + "Let P(v) = (v₀,v₁,v₂). In ℝ³ take the six lines spanned, in order, by "
                + "(0,1,0), (1,1,0), (1,−1,0), (0,0,1), (1,0,1) and (1,0,−1). "
                + "Define R(v,t) by requiring that P(v) = 0 or P(t) = 0 or the two projections lie on a common one of these lines, "
                + "together with v₃t₂ = t₃v₂ = v₄t₁ = t₄v₁ = 0.")),
        Paragraph(Text(
            "A nonzero vector of ℝ³ belongs to at most one of the six lines: equating scalar multiples of their directions "
                + "and comparing their three coordinates proves this for each pair of directions. "
                + "Consequently, for fixed v, the projected part of its polar is all of E when P(v) = 0, "
                + "the inverse image of the unique line containing P(v) when there is such a line, "
                + "and the kernel of P otherwise. Each is a subspace. The four additional equations are linear in t, "
                + "so the full singleton polar is a subspace. The relation is symmetric and relates zero to zero. "
                + "The polar of any set is the intersection of its singleton polars, hence R makes E a locality vector space.")),
        Paragraph(Text(
            "Write [v,t] for the single generator at the pair (v,t), with real coefficient one, and eᵢ for the coordinate vectors. "
                + "For k = 1,2 put Aₖ = ½[e₀ + eₖ,e₀ + eₖ] + ½[e₀ − eₖ,e₀ − eₖ] − [eₖ,eₖ], "
                + "and put c₃ = [e₃,e₃], c₄ = [e₄,e₄]. All generators of A₁ and A₂ are local: "
                + "their projections have one of the six specified directions and their last two coordinates vanish. "
                + "The generators c₃ and c₄ are also local because their projections vanish. "
                + "Thus these four elements lie in the free span of local pairs.")),
        Paragraph(Text(
            "Expanding the two additivity relations and the scalar relations for multiplication by −1 "
                + "shows that Aₖ − [e₀,e₀] belongs to the ambient bilinearity submodule. "
                + "More explicitly, expand [e₀ + eₖ,e₀ + eₖ] in both entries, "
                + "expand [e₀ − eₖ,e₀ − eₖ] in the same way, and replace terms with a negative entry by their scalar relations. "
                + "Half their sum is congruent to [e₀,e₀] + [eₖ,eₖ]. "
                + "Subtracting the identities for k = 2 and k = 1 gives A₂ − A₁ in that submodule. "
                + "Its local support places the difference in the intersection defining the bilinearity subspace. "
                + "Checking the three possible support pairs of each Aₖ also gives that A₁ is support-related to c₃ "
                + "and A₂ is support-related to c₄ under both generator relations. "
                + "Every generator used here is diagonal, of the form (v,v). Local support supplies R(v,v), "
                + "so the componentwise cross relation supplies all four cross pairs and the local diagonal pairs "
                + "supply the remaining two conditions of four-way locality.")),
        Paragraph(Text(
            "For each i in Fin 5, extend [v,t] ↦ vᵢtᵢ linearly to a real functional Fᵢ on the ambient free span. "
                + "Each functional vanishes on every bilinearity generator by distributivity and scalar multiplication; "
                + "linearity then makes it vanish on their entire span. Direct evaluation gives "
                + "F₀(A₁) = 1, F₃(c₃) = 1, F₄(c₄) = 1, and F₃(c₃ + c₄) = F₄(c₃ + c₄) = 1. "
                + "Whenever Fᵢ of a finitely supported element is nonzero, some pair (v,t) in its support has vᵢtᵢ nonzero, "
                + "since otherwise every term in its defining finite sum would vanish.")),
        Paragraph(Text(
            "If R(v,t) and v₀t₀ ≠ 0, neither projection vanishes. A common line must then be one of those "
                + "whose direction has first coordinate one, so v₁ ≠ 0 or v₂ ≠ 0. "
                + "Now suppose a,b,c have local support, F₀(a) ≠ 0, F₃(b) ≠ 0 and F₄(c) ≠ 0, "
                + "and a is support-related to both b and c. Choose support pairs (v,t) of a, (u,s) of b "
                + "and (h,j) of c with v₀t₀ ≠ 0, u₃s₃ ≠ 0 and h₄j₄ ≠ 0. "
                + "Either generator relation implies componentwise relatedness, giving R(v,u) and R(v,h). "
                + "The equations u₃v₂ = 0 and h₄v₁ = 0 force v₂ = v₁ = 0. "
                + "But the pair (v,t) has local support, contradicting the preceding alternative. "
                + "Finally, equality of quotient classes makes the difference of representatives lie in the bilinearity subspace, "
                + "so every Fᵢ has equal values on equal quotient classes.")),
        Paragraph(Text(
            "To refute locality compatibility, take x = A₁, x′ = A₂, y = c₃, z = c₄ and w = x′ − x. "
                + "The element w belongs to the bilinearity subspace, x is related to y, "
                + "and x + w = x′ is related to z. Compatibility would supply an adjustment w′ in that subspace "
                + "such that x + w′ is related to both y and z. Yet F₀(x + w′) = F₀(A₁) = 1, "
                + "while F₃(y) = F₄(z) = 1. The obstruction for the three elements x + w′, y, z gives a contradiction.")),
        Paragraph(Text(
            "For the tensor-product conjecture, let q be the quotient map. Since A₂ − A₁ belongs to its kernel, "
                + "q(A₂) = q(A₁). The related representatives already found imply that q(A₁) is related to both q(c₃) and q(c₄). "
                + "If the quotient relation were a locality vector-space relation, the polar of the singleton {q(A₁)} "
                + "would be a subspace. Closure under addition would make q(A₁) related to q(c₃ + c₄). "
                + "Choose related representatives a,b of these two classes. Invariance of the functionals on classes gives "
                + "F₀(a) = 1 and F₃(b) = F₄(b) = 1. Applying the same obstruction to a,b,b is impossible. "
                + "Both arguments apply to each generator relation: diagonal generators provide the positive relations, "
                + "and projection to componentwise locality gives the same obstruction. "
                + "Thus both conjectures are false for both relations, negating the four-term disjunction.")));

    private static Formula LocalityVectorSpaceFormula()
    {
        Formula symmetry = All("x", X("E"), All("y", X("E"),
            Arrow(Rel("x", "y"), Rel("y", "x"))));
        Formula polar = All("U", SetOf(X("E")), Some("S", SubmoduleOf(X("E")),
            Equal(At(Qualified("SetLike", "coe"), X("S")),
                SetWhere("x", X("E"), All("u", X("E"),
                    Arrow(Member(X("u"), X("U")), Rel("u", "x")))))));
        return VectorBinders(All("r", RelationOn(X("E")),
            IffOf(LocalCall("IsLocalityVectorSpace", X("K"), X("r")),
                AndOf(symmetry, AndOf(At(X("r"), Typed(D(0), X("E")), Typed(D(0), X("E"))), polar)))));
    }

    private static Formula LocalityProductFormula()
    {
        Formula first = At(Qualified("Prod", "fst"), X("p"));
        Formula second = At(Qualified("Prod", "snd"), X("p"));
        return Parameters(Equal(Typed(LocalCall("localityProduct", X("r"), X("V"), X("W")), SetOf(Pairs())),
            SetWhere("p", Pairs(), AndOf(Member(first, X("V")),
                AndOf(Member(second, X("W")), At(X("r"), first, second))))));
    }

    private static Formula SpanRelationFormula()
    {
        Formula body = All("x", X("X"), Arrow(Member(X("x"), At(Qualified("Finsupp", "support"), X("a"))),
            All("y", X("X"), Arrow(Member(X("y"), At(Qualified("Finsupp", "support"), X("b"))),
                At(X("s"), X("x"), X("y"))))));
        return All("K", Qualified("Type"), All("X", Qualified("Type"),
            Instance(At(Qualified("Zero"), X("K")), All("s", RelationOn(X("X")),
                All("a", FinsuppOf(X("X")), All("b", FinsuppOf(X("X")),
                    IffOf(LocalCall("spanRel", X("s"), X("a"), X("b")), body)))))));
    }

    private static Formula BilinearRelationsFormula()
    {
        Formula a = X("a"), b = X("b"), x = X("x"), y = X("y"), k = X("k"), f = X("f");
        Formula leftAdd = InSubspace("a", "V", InSubspace("b", "V", InSubspace("x", "W",
            Equal(f, Subtract(Subtract(Single(Add(a, b), x), Single(a, x)), Single(b, x))))));
        Formula rightAdd = InSubspace("a", "V", InSubspace("x", "W", InSubspace("y", "W",
            Equal(f, Subtract(Subtract(Single(a, Add(x, y)), Single(a, x)), Single(a, y))))));
        Formula leftScale = InSubspace("a", "V", InSubspace("x", "W", Some("k", X("K"),
            Equal(f, Subtract(Single(Smul(k, a), x), Smul(k, Single(a, x)))))));
        Formula rightScale = InSubspace("a", "V", InSubspace("x", "W", Some("k", X("K"),
            Equal(f, Subtract(Single(a, Smul(k, x)), Smul(k, Single(a, x)))))));
        return VectorBinders(SubspaceBinders(Equal(
            Typed(LocalCall("bilRelations", X("V"), X("W")), SubmoduleOf(Ambient())),
            At(Qualified("Submodule", "span"), X("K"), SetWhere("f", Ambient(),
                OrOf(leftAdd, OrOf(rightAdd, OrOf(leftScale, rightScale))))))));
    }

    private static Formula FreeSpanFormula() => Parameters(Equal(
        Typed(Free(), SubmoduleOf(Ambient())),
        At(Qualified("Finsupp", "supported"), X("K"), X("K"),
            LocalCall("localityProduct", X("r"), X("V"), X("W")))));

    private static Formula BilinearIdealFormula() => Parameters(Equal(
        Typed(Ideal(), SubmoduleOf(Ambient())),
        At(Qualified("Min", "min"), LocalCall("bilRelations", X("V"), X("W")), Free())));

    private static Formula LocalityTensorFormula() => Parameters(Equal(
        Typed(Tensor(), Qualified("Type")),
        At(Qualified("HasQuotient", "Quotient"), FreeType(), IdealInFree())));

    private static Formula FourWayFormula()
    {
        Formula p1 = At(Qualified("Prod", "fst"), X("p"));
        Formula p2 = At(Qualified("Prod", "snd"), X("p"));
        Formula q1 = At(Qualified("Prod", "fst"), X("q"));
        Formula q2 = At(Qualified("Prod", "snd"), X("q"));
        Formula R(Formula a, Formula b) => At(X("r"), a, b);
        return All("E", Qualified("Type"), All("r", RelationOn(X("E")),
            All("p", Pairs(), All("q", Pairs(),
                IffOf(LocalCall("fourWay", X("E"), X("r"), X("p"), X("q")),
                    AndOf(R(p1, p2), AndOf(R(p1, q1), AndOf(R(p1, q2),
                        AndOf(R(p2, q1), AndOf(R(p2, q2), R(q1, q2)))))))))));
    }

    private static Formula QuotientRelationFormula()
    {
        Formula relation = LambdaOf("u", FreeType(), LambdaOf("v", FreeType(),
            LocalCall("spanRel", X("s"), Value("u"), Value("v"))));
        Formula body = IffOf(LocalCall("quotientRel", X("r"), X("s"), X("V"), X("W"), X("a"), X("b")),
            At(Qualified("Relation", "Map"), relation,
                Qualified("Submodule", "Quotient", "mk"), Qualified("Submodule", "Quotient", "mk"),
                X("a"), X("b")));
        return VectorBinders(All("r", RelationOn(X("E")), All("s", RelationOn(Pairs()),
            SubspaceBinders(All("a", Tensor(), All("b", Tensor(), body))))));
    }

    private static Formula LocalityCompatibleFormula()
    {
        Formula conclusion = Some("w'", X("E"), AndOf(Member(X("w'"), X("W")),
            AndOf(At(X("r"), Add(X("x"), X("w'")), X("y")),
                At(X("r"), Add(X("x"), X("w'")), X("z")))));
        Formula body = All("x", X("E"), All("y", X("E"), All("z", X("E"), All("w", X("E"),
            Arrow(Member(X("w"), X("W")), Arrow(Rel("x", "y"),
                Arrow(At(X("r"), Add(X("x"), X("w")), X("z")), conclusion)))))));
        return VectorBinders(All("r", RelationOn(X("E")), All("W", SubmoduleOf(X("E")),
            IffOf(LocalCall("LocalityCompatible", X("r"), X("W")), body))));
    }

    private static Formula TensorConjectureFormula() => All("s", RelationRule(),
        IffOf(LocalCall("TensorConjecture", X("s")),
            Parameters(Arrow(LocalCall("IsLocalityVectorSpace", X("K"), X("r")),
                LocalCall("IsLocalityVectorSpace", X("K"),
                    LocalCall("quotientRel", X("r"), RuleRelation(), X("V"), X("W")))), characteristicZero: true)));

    private static Formula PairConjectureFormula()
    {
        Formula relation = LambdaOf("a", FreeType(), LambdaOf("b", FreeType(),
            LocalCall("spanRel", RuleRelation(), Value("a"), Value("b"))));
        return All("s", RelationRule(), IffOf(LocalCall("PairConjecture", X("s")), Parameters(
            Arrow(LocalCall("IsLocalityVectorSpace", X("K"), X("r")),
                LocalCall("LocalityCompatible", relation, IdealInFree())), characteristicZero: true)));
    }

    private static Formula ClaimFormula() => IffOf(Local("claim"),
        OrOf(LocalCall("TensorConjecture",
                LambdaOf("E", Qualified("Type"), LambdaOf("r", RelationOn(X("E")), ProductRelation()))),
            OrOf(LocalCall("TensorConjecture", Local("fourWay")),
                OrOf(LocalCall("PairConjecture",
                        LambdaOf("E", Qualified("Type"), LambdaOf("r", RelationOn(X("E")), ProductRelation()))),
                    LocalCall("PairConjecture", Local("fourWay"))))));

    private static Formula RelationRule() => All("E", Qualified("Type"),
        Arrow(RelationOn(X("E")), RelationOn(Pairs())));
    private static Formula RuleRelation() => At(X("s"), X("E"), X("r"));

    private static Formula X(string name) => name == "w'" ? Seq(F.Id("w"), Apos) : F.Id(name);
    private static Formula Qualified(params string[] parts) =>
        Seq(Operatorname, Grp(Seq([.. parts.SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Local(string name) => Qualified("D5", "S3", "HomologicalAlgebra",
        "LocalityTensorProductRefutation", name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula VectorBinders(Formula body, bool characteristicZero = false)
    {
        Formula vectorSpace = Instance(At(Qualified("AddCommGroup"), X("E")),
            Instance(At(Qualified("Module"), X("K"), X("E")), body));
        return All("K", Qualified("Type"), All("E", Qualified("Type"),
            Instance(At(Qualified("Field"), X("K")), characteristicZero
                ? Instance(At(Qualified("CharZero"), X("K")), vectorSpace) : vectorSpace)));
    }
    private static Formula SubspaceBinders(Formula body) => All("V", SubmoduleOf(X("E")), All("W", SubmoduleOf(X("E")), body));
    private static Formula Parameters(Formula body, bool characteristicZero = false) =>
        VectorBinders(All("r", RelationOn(X("E")), SubspaceBinders(body)), characteristicZero);
    private static Formula RelationOn(Formula type) => Arrow(type, Arrow(type, Qualified("Prop")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula AndOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula OrOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula SetOf(Formula type) => At(Qualified("Set"), type);
    private static Formula SetWhere(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Typed(X(name), type), Sp, Mid, Sp, Parenthesized(body), CloseBrace);
    private static Formula SubmoduleOf(Formula type) => At(Qualified("Submodule"), X("K"), type);
    private static Formula Pairs() => Seq(X("E"), Sp, Times, Sp, X("E"));
    private static Formula FinsuppOf(Formula type) => At(Qualified("Finsupp"), type, X("K"));
    private static Formula Ambient() => FinsuppOf(Parenthesized(Pairs()));
    private static Formula Free() => LocalCall("freeSpan", X("r"), X("V"), X("W"));
    private static Formula FreeType() => At(Qualified("CoeSort", "coe"), Free());
    private static Formula Ideal() => LocalCall("bilIdeal", X("r"), X("V"), X("W"));
    private static Formula IdealInFree() => At(Qualified("Submodule", "comap"),
        At(Qualified("Submodule", "subtype"), Free()), Ideal());
    private static Formula Tensor() => LocalCall("localityTensor", X("r"), X("V"), X("W"));
    private static Formula ProductRelation() => At(Qualified("Prod", "RProd"), X("r"), X("r"));
    private static Formula Value(string name) => At(Qualified("Subtype", "val"), X(name));
    private static Formula Rel(string a, string b) => At(X("r"), X(a), X(b));
    private static Formula InSubspace(string name, string subspace, Formula body) =>
        Some(name, X("E"), AndOf(Member(X(name), X(subspace)), body));
    private static Formula Single(Formula a, Formula x) => At(Qualified("Finsupp", "single"), Pair(a, x), Typed(D(1), X("K")));
    private static Formula Smul(Formula scalar, Formula vector) => At(Qualified("HSMul", "hSMul"), scalar, vector);
}
