using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class BitThreadIngletonMultiflowRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/BitThreadIngletonMultiflowRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Entropy/baoharper2020hypergraphs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A capacitated star separates the Ingleton combination of minimum cuts from that of a max multiflow.",
        H("An Ingleton counterexample for max multiflows"),
        Blocks(
            Definition("cut-value", "cutValue", "The capacity of a vertex cut", CutValueFormula(),
                AssessedProvenance.FromRepo(Source),
                "For a real capacity function cap on a finite vertex type vtx, cutValue cap w sums "
                    + "the capacities directed from w to its complement. Each ordered pair contributes "
                    + "cap u v exactly when u lies in w and v does not. No symmetry or positivity is "
                    + "required by this definition."),
            Definition("admissible-cuts", "admissibleCuts", "Cuts with a prescribed boundary side",
                AdmissibleCutsFormula(), AssessedProvenance.FromRepo(Source),
                "The embedding b labels k distinct boundary vertices. An admissible cut for s "
                    + "contains precisely the labelled boundary vertices whose indices belong to s; "
                    + "membership of every other vertex is unrestricted. Filtering all vertex subsets "
                    + "gives a finite collection of such cuts."),
            Definition("min-cut", "minCut", "The minimum boundary cut", MinCutFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The entropy of s is the least capacity among its admissible vertex cuts. "
                    + "The collection is nonempty because the image of s under b is an admissible cut. "
                    + "Thus the finite minimum exists even for arbitrary real capacities and an empty "
                    + "boundary. This is the finite graph form of the source's minimum-cut entropy "
                    + "in the footnote at BT_Hyper.tex line 417."),
            Definition("is-multiflow", "IsMultiflow", "Pair flows with a shared capacity bound",
                IsMultiflowFormula(), AssessedProvenance.FromLiterature(Source),
                "For each boundary pair i < j, f i j is antisymmetric in its vertex arguments and "
                    + "has zero divergence away from b i and b j. Its divergences at those endpoints "
                    + "are respectively n i j and minus n i j, with n i j nonnegative. On every ordered "
                    + "vertex pair, the sum of the absolute pair-flow values is at most cap u v. "
                    + "Entries with i not less than j do not contribute to this load or impose flow "
                    + "conditions. These are finite graph versions of the multiflow constraints in "
                    + "BT_Hyper.tex lines 100–107, with the endpoint fluxes written explicitly."),
            Definition("subflow", "subflow", "Threads crossing a boundary region", SubflowFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The subflow of s sums the thread numbers for pairs with one boundary index in s "
                    + "and the other outside. The lesser index is always the first argument of n, "
                    + "so each crossing pair is counted once. This is Definition 1 in BT_Hyper.tex "
                    + "lines 110–115, using one representative of each unordered pair."),
            Definition("is-max-multiflow", "IsMaxMultiflow", "Simultaneous singleton saturation",
                IsMaxMultiflowFormula(), AssessedProvenance.FromLiterature(Source),
                "A max multiflow is a multiflow whose subflow at each singleton equals the "
                    + "minimum cut for that singleton. This is the saturation condition of Theorem 1 "
                    + "in BT_Hyper.tex lines 117–124. No saturation of larger boundary regions is "
                    + "included in the predicate."),
            Definition("claim", "claim", "The proposed equality for every max multiflow", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For every finite vertex type, every natural boundary size, every symmetric "
                    + "loopless nonnegative real capacity function, every boundary embedding and "
                    + "every real coefficient family, consider the same linear functional of minimum "
                    + "cuts and of subflows. If the functional is nonnegative on every multiflow and "
                    + "nonzero on at least one, the proposed conclusion equates its minimum-cut "
                    + "value with its value on every max multiflow. The coefficients are unrestricted "
                    + "real numbers; the source writes their positive and negative parts separately "
                    + "at BT_Hyper.tex lines 409–416. This is the finite graph reading of Conjecture 1 "
                    + "at lines 419–424; the footnote at line 417 includes 2-graphs among its geometries."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A five-boundary star refutes the equality"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use the six vertices 0, 1, 2, 3, 4, 5, with centre 5 and boundary labels "
                            + "A, B, C, D, E at 0, 1, 2, 3, 4. The boundary embedding is the natural "
                            + "inclusion of Fin 5 into Fin 6. The four edges from the centre to "
                            + "A, B, C, D have capacity 1, and the edge to E has capacity 2, in both "
                            + "directions; all other capacities are zero. For a boundary region I, "
                            + "let w(I) sum these boundary capacities, whose total is 6.")),
                    Paragraph(Text(
                        "Choose the linear functional R(x) = x(AB) + x(AC) + x(AD) + x(BC) + x(BD) "
                            + "− x(A) − x(B) − x(CD) − x(ABC) − x(ABD), where juxtaposed labels denote "
                            + "their union. Expanding its coefficients first gives this ten-term "
                            + "expression for every region function x. Substituting the definition of "
                            + "subflow and collecting each pair's contributions then gives "
                            + "R(subflow n) = 2 n 0 1 + 2 n 2 3 for every real thread-number family n. "
                            + "The other eight unordered pairs have coefficient zero. The source "
                            + "also gives this 2-graph identity at BT_Hyper.tex lines 395–399.")),
                    Paragraph(Text(
                        "For any admissible vertex cut W of I, its capacity is w(I) when the centre "
                            + "is outside W, and 6 − w(I) when the centre is inside W. Both cases "
                            + "are attained: take the boundary image of I alone, or add the centre. "
                            + "These two cuts give the upper bounds for the minimum, while the "
                            + "two-case expression bounds every admissible cut from below. "
                            + "Consequently minCut(I) = min(w(I), 6 − w(I)).")),
                    Paragraph(Text(
                        "Set n 0 1 = n 2 4 = n 3 4 = 1 and all other entries to zero. For each "
                            + "selected pair, send one unit along the two-edge path from its smaller "
                            + "boundary vertex through the centre to its larger boundary vertex, "
                            + "and assign the negatives on reversed edges. All unselected pair flows "
                            + "are zero. Checking the finite vertex and pair cases establishes "
                            + "antisymmetry, zero divergence away from the two endpoints, endpoint "
                            + "divergences equal to the prescribed nonnegative thread numbers and "
                            + "the shared capacity bounds. The edge loads are 1, 1, 1, 1, 2, "
                            + "respectively. The singleton subflows are also 1, 1, 1, 1, 2; applying "
                            + "the minimum-cut formula at each singleton shows that this is a max multiflow.")),
                    Paragraph(Text(
                        "Evaluating the ten minimum cuts gives 2, 2, 2, 2, 2 for the positive "
                            + "terms and 1, 1, 2, 3, 3 for the negative terms. Hence R(minCut) = 0. "
                            + "The pair-coefficient identity gives R(subflow n) = 2 for the chosen "
                            + "threads. For an arbitrary multiflow, its nonnegative thread numbers "
                            + "at pairs (0,1) and (2,3), together with the same identity, give "
                            + "R(subflow n) ≥ 0. The capacity function is symmetric, vanishes on "
                            + "the diagonal and is nonnegative, as its explicit finite values show.")),
                    Paragraph(Text(
                        "Assuming claim, apply it to this graph, its five boundary vertices and R. "
                            + "Universal nonnegativity supplies the first functional hypothesis; "
                            + "the constructed multiflow with value 2 supplies the nonzero example. "
                            + "Applying the resulting equality to that same max multiflow yields "
                            + "0 = 2, a contradiction. Thus the proposed equality fails already for "
                            + "a finite 2-graph and the Ingleton combination named in BT_Hyper.tex "
                            + "line 426. Its minimum-cut value here is zero, so the counterexample "
                            + "does not violate the Ingleton inequality itself."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bao-harper-2020-bit-thread-ingleton-multiflow"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CutValueFormula() => VertexBinders(
        All("cap", CapacityType(), All("w", FinsetOf(X("vtx")),
            Equal(Typed(LocalCall("cutValue", X("cap"), X("w")), Reals()),
                SumOver("u", X("vtx"), SumOver("v", X("vtx"),
                    If(And(Member(X("u"), X("w")), NotMember(X("v"), X("w"))),
                        At(X("cap"), X("u"), X("v")), RealZero())))))));

    private static Formula AdmissibleCutsFormula() => BoundaryBinders(
        All("b", BoundaryType(), All("s", RegionType(),
            Equal(Typed(LocalCall("admissibleCuts", X("b"), X("s")), FinsetOf(FinsetOf(X("vtx")))),
                At(Qualified("Finset", "filter"),
                    LambdaOf("w", FinsetOf(X("vtx")), All("i", FinK(),
                        IffOf(Member(At(X("b"), X("i")), X("w")), Member(X("i"), X("s"))))),
                    Typed(Qualified("Finset", "univ"), FinsetOf(FinsetOf(X("vtx")))))))));

    private static Formula MinCutFormula()
    {
        Formula values = At(Qualified("Finset", "image"), LocalCall("cutValue", X("cap")),
            LocalCall("admissibleCuts", X("b"), X("s")));
        return BoundaryBinders(All("cap", CapacityType(), All("b", BoundaryType(),
            All("s", RegionType(), Equal(Typed(LocalCall("minCut", X("cap"), X("b"), X("s")), Reals()),
                At(Seq(Qualified("Finset", "min"), Apos), values))))));
    }

    private static Formula IsMultiflowFormula()
    {
        Formula ordered = LT(X("i"), X("j"));
        Formula antisymmetry = All("i", FinK(), All("j", FinK(), All("u", X("vtx"),
            All("v", X("vtx"), Arrow(ordered,
                Equal(At(X("f"), X("i"), X("j"), X("u"), X("v")),
                    new Formula.Negate(At(X("f"), X("i"), X("j"), X("v"), X("u")))))))));
        Formula conservation = All("i", FinK(), All("j", FinK(), All("u", X("vtx"),
            Arrow(ordered, Arrow(NotEqual(X("u"), At(X("b"), X("i"))),
                Arrow(NotEqual(X("u"), At(X("b"), X("j"))),
                    Equal(SumOver("v", X("vtx"), At(X("f"), X("i"), X("j"), X("u"), X("v"))),
                        RealZero())))))));
        Formula endpoints = All("i", FinK(), All("j", FinK(), Arrow(ordered,
            And(LE(RealZero(), At(X("n"), X("i"), X("j"))),
                And(Equal(SumOver("v", X("vtx"),
                        At(X("f"), X("i"), X("j"), At(X("b"), X("i")), X("v"))),
                        At(X("n"), X("i"), X("j"))),
                    Equal(SumOver("v", X("vtx"),
                        At(X("f"), X("i"), X("j"), At(X("b"), X("j")), X("v"))),
                        new Formula.Negate(At(X("n"), X("i"), X("j")))))))));
        Formula load = All("u", X("vtx"), All("v", X("vtx"),
            LE(SumOver("i", FinK(), SumOver("j", FinK(),
                    If(ordered, new Formula.Absolute(At(X("f"), X("i"), X("j"), X("u"), X("v"))),
                        RealZero()))), At(X("cap"), X("u"), X("v")))));
        return MultiflowBinders(IffOf(LocalCall("IsMultiflow", X("cap"), X("b"), X("f"), X("n")),
            And(antisymmetry, And(conservation, And(endpoints, load)))));
    }

    private static Formula SubflowFormula() => All("k", Naturals(), All("n", ThreadType(),
        All("s", RegionType(), Equal(Typed(LocalCall("subflow", X("n"), X("s")), Reals()),
            SumIn("i", FinK(), X("s"), SumOver("j", FinK(),
                If(NotMember(X("j"), X("s")),
                    If(LT(X("i"), X("j")), At(X("n"), X("i"), X("j")),
                        At(X("n"), X("j"), X("i"))), RealZero())))))));

    private static Formula IsMaxMultiflowFormula() => MultiflowBinders(
        IffOf(LocalCall("IsMaxMultiflow", X("cap"), X("b"), X("f"), X("n")),
            And(LocalCall("IsMultiflow", X("cap"), X("b"), X("f"), X("n")),
                All("i", FinK(), Equal(LocalCall("subflow", X("n"), Singleton(X("i"))),
                    LocalCall("minCut", X("cap"), X("b"), Singleton(X("i"))))))));

    private static Formula ClaimFormula()
    {
        Formula symmetry = All("u", X("vtx"), All("v", X("vtx"),
            Equal(At(X("cap"), X("u"), X("v")), At(X("cap"), X("v"), X("u")))));
        Formula loopless = All("u", X("vtx"), Equal(At(X("cap"), X("u"), X("u")), RealZero()));
        Formula nonnegative = All("u", X("vtx"), All("v", X("vtx"),
            LE(RealZero(), At(X("cap"), X("u"), X("v")))));
        Formula multiflow = LocalCall("IsMultiflow", X("cap"), X("b"), X("f"), X("n"));
        Formula subflowValue = At(Qualified("dotProduct"), Alpha, LocalCall("subflow", X("n")));
        Formula allNonnegative = All("f", FlowType(), All("n", ThreadType(),
            Arrow(multiflow, GE(subflowValue, RealZero()))));
        Formula someNonzero = Some("f", FlowType(), Some("n", ThreadType(),
            And(multiflow, NotEqual(subflowValue, RealZero()))));
        Formula equality = All("f", FlowType(), All("n", ThreadType(),
            Arrow(LocalCall("IsMaxMultiflow", X("cap"), X("b"), X("f"), X("n")),
                Equal(At(Qualified("dotProduct"), Alpha, LocalCall("minCut", X("cap"), X("b"))),
                    subflowValue))));
        return IffOf(Local("claim"), BoundaryBinders(All("cap", CapacityType(),
            All("b", BoundaryType(), All("α", Arrow(RegionType(), Reals()),
                Arrow(symmetry, Arrow(loopless, Arrow(nonnegative,
                    Arrow(allNonnegative, Arrow(someNonzero, equality))))))))));
    }

    private static Formula VertexBinders(Formula body) => All("vtx", Qualified("Type"),
        Seq(OpenBracket, At(Qualified("Fintype"), X("vtx")), CloseBracket, Sp,
            OpenBracket, At(Qualified("DecidableEq"), X("vtx")), CloseBracket, Comma, Sp,
            Parenthesized(body)));
    private static Formula BoundaryBinders(Formula body) => VertexBinders(All("k", Naturals(), body));
    private static Formula MultiflowBinders(Formula body) => BoundaryBinders(All("cap", CapacityType(),
        All("b", BoundaryType(), All("f", FlowType(), All("n", ThreadType(), body)))));
    private static Formula CapacityType() => Arrow(X("vtx"), Arrow(X("vtx"), Reals()));
    private static Formula BoundaryType() => At(Qualified("Function", "Embedding"), FinK(), X("vtx"));
    private static Formula FlowType() => Arrow(FinK(), Arrow(FinK(), CapacityType()));
    private static Formula ThreadType() => Arrow(FinK(), Arrow(FinK(), Reals()));
    private static Formula RegionType() => FinsetOf(FinK());
    private static Formula FinK() => At(Qualified("Fin"), X("k"));
    private static Formula FinsetOf(Formula type) => At(Qualified("Finset"), type);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula RealZero() => Typed(D(0), Reals());
    private static Formula X(string name) => name == "α" ? Alpha : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Entropy",
        "BitThreadIngletonMultiflowRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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

    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula type, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Typed(X(name), type), Sp, InMacro, Sp, set)), Sp,
            Parenthesized(body));
    private static Formula Singleton(Formula value) => Seq(OpenBrace, value, CloseBrace);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), condition, yes, no);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula GE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula NotMember(Formula value, Formula set) => new Formula.Not(Parenthesized(Member(value, set)));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
