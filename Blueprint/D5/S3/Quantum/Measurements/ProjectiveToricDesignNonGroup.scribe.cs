using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ProjectiveToricDesignNonGroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/iosuemooneyehrenberggorshkov2024toric");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An identity-containing projective toric two-design in dimension 27 satisfies the MUB overlap condition without being a group.",
        H("A projective toric design without additive closure"),
        Blocks(
            Node("design2", "The second moment condition", DesignFormula(),
                "The angles lie in Real.Angle, the additive circle ℝ/(2πℤ). Real.Angle.toCircle sends an angle to its unit complex exponential; Subtype.val includes that circle element in ℂ. "
                    + "For each four coordinate indices, the sum is the complex cast of the cardinality when the two index pairs agree as multisets, and is complex zero otherwise. "
                    + "This is the uniformly weighted second moment equation multiplied by the cardinality, from main.tex lines 198–206, equation eq:repr-proj-toric. "
                    + "The predicate itself allows every natural d and every finite X, including the empty set, and does not impose a zero first coordinate.",
                AssessedProvenance.FromLiterature(Source)),
            Node("mubOverlap", "The unnormalized overlap condition", OverlapFormula(),
                "For distinct phase functions φ and θ in X, the squared complex norm of their exponential sum is either real zero or the real cast of d. "
                    + "The sum ranges over all j in Fin d. This is equation eq:toric-angle in main.tex lines 654–657. "
                    + "There is no positivity or cardinality hypothesis in this predicate.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The subgroup conjecture with the identity included", ClaimFormula(),
                "The conjecture in main.tex lines 783–788 says that a projective toric two-design of size d² satisfying the overlap condition must be a subgroup. "
                    + "Here d is positive, the representative of every projective point has coordinate zero equal to zero, and the design is additionally required to contain the zero phase function. "
                    + "The representative slice identifies the projective torus with the additive subgroup {0} × T^(d−1) of T^d, so the conclusion asks for an additive subgroup of the full phase-function space with carrier exactly X. "
                    + "The condition that zero belong to X weakens the universal assertion in the source; it excludes a failure caused solely by translating a group away from its identity. "
                    + "Positivity ensures that coordinate zero belongs to Fin d. SetLike.coe explicitly gives both carriers in the concluding equality.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("projective-toric-nongroup-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A non-group design with 729 points"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Index the 27 coordinates by x in (ZMod 3)³, using the base-three equivalence from Fin 27, which sends coordinate zero to the zero vector. "
                            + "Let χ be ZMod.stdAddChar and let an element k of ZMod 3 determine the angle 2π times the real cast of k.val, divided by 3, modulo 2π. This map is additive and injective, and its complex exponential is χ(k). "
                            + "Use 27 symmetric matrices Mᵢ over ZMod 3. In order i = 0,…,26, their upper triangular entries (M₀₀,M₀₁,M₀₂,M₁₁,M₁₂,M₂₂) are "
                            + "(0,0,0,0,0,0), (0,1,2,1,2,0), (0,2,1,2,1,0), (0,0,2,2,1,2), "
                            + "(1,1,1,0,2,2), (1,2,2,0,2,1), (0,0,1,1,2,1), (2,1,1,0,1,2), "
                            + "(2,2,2,0,1,1), (2,0,2,2,0,0), (1,2,0,1,2,2), (1,2,1,2,0,1), "
                            + "(1,1,2,2,2,2), (2,2,0,2,2,0), (0,2,2,1,0,1), (0,1,0,0,0,1), "
                            + "(2,0,1,0,2,0), (1,0,0,2,2,1), (1,0,1,1,0,0), (2,1,2,1,0,2), "
                            + "(2,1,0,2,1,1), (0,2,0,0,0,2), (2,0,0,1,1,2), (1,0,2,0,1,0), "
                            + "(2,2,1,1,1,1), (0,1,1,2,0,2), and (1,1,0,1,1,0). "
                            + "For each i in Fin 27 and b in (ZMod 3)³, define the phase function by the angle of xᵀMᵢx + b·x, and let X be the set of these functions. "
                            + "Finite arithmetic verifies symmetry, det(Mᵢ − Mⱼ) ≠ 0 for i ≠ j, and that no listed matrix equals M₁ + M₃.")),
                    Paragraph(Text(
                        "Character orthogonality gives Σₓχ(w·x) = 27 for w = 0 and zero otherwise. Indeed, for w ≠ 0, the character x ↦ χ(w·x) is nontrivial: "
                            + "if it were trivial, injectivity of χ would force w·x = 0 for every x and hence w = 0. "
                            + "Writing q(x) = xᵀMx + b·x for a symmetric matrix M, expansion gives q(h + y) − q(y) = q(h) + (2My)·h = q(h) + (2Mh)·y. "
                            + "When det M ≠ 0, the squared norm of Σₓχ(q(x)) is its product with the conjugate sum. "
                            + "Reindex that double sum by x = h + y and use the shift identity. The inner sum becomes Σᵧχ((2Mh)·y). "
                            + "Since M is invertible and 2 is nonzero in ZMod 3, only h = 0 contributes, giving squared norm 27.")),
                    Paragraph(Text(
                        "For every nonzero g, the map i ↦ Mᵢg is injective: equality for distinct i and j would put g in the kernel of the invertible difference Mᵢ − Mⱼ. "
                            + "Both its domain and codomain have 27 elements, so it is bijective. "
                            + "Also, a symmetric quadratic polynomial xᵀAx + b·x determines A and b uniquely as functions on (ZMod 3)³. "
                            + "Subtracting its values at x and y from its value at x + y determines 2xᵀAy. Since 2 ≠ 0, equality of two such polynomials gives equality of their bilinear forms, hence A = B; the remaining linear terms then give b = c.")),
                    Paragraph(Text(
                        "For two distinct parameter pairs (i,b) and (k,c), equal matrix indices leave the nonzero linear form (b − c)·x, whose character sum vanishes. "
                            + "Different matrix indices leave the symmetric quadratic form with matrix Mᵢ − Mₖ and linear term b − c. Its matrix is invertible, so the preceding squared-norm calculation gives 27. "
                            + "Thus every two distinct parameter pairs have squared exponential overlap zero or 27.")),
                    Paragraph(Text(
                        "For the second moment, sum first over the linear parameter c. Set s = a₁ + a₂ − b₁ − b₂ in (ZMod 3)³. "
                            + "If the two index pairs agree as multisets, every exponent is zero and the double sum is 729. "
                            + "Otherwise the double sum factors as the sum of the quadratic phases over i times 27 when s = 0, or times zero when s ≠ 0, by character orthogonality. "
                            + "In the remaining case s = 0, symmetry gives the quadratic phase 2(a₁ − b₁)ᵀMᵢ(a₁ − b₂). "
                            + "Both a₁ − b₁ and a₁ − b₂ are nonzero, since either equality would make the two pairs agree. "
                            + "Reindex the sum over i by the bijection i ↦ Mᵢ(a₁ − b₂). It becomes the character sum of the nonzero linear form 2(a₁ − b₁)·y and is zero. "
                            + "This proves both cases of the required moment identity.")),
                    Paragraph(Text(
                        "The phase functions belonging to distinct parameter pairs are distinct. If two were equal, injectivity of the angle map would make their exponent polynomials equal at every x. "
                            + "Their overlap sum would then be 27, with squared norm 729, contradicting the values zero and 27 just obtained. "
                            + "Every phase function vanishes at coordinate zero because the corresponding vector x is zero. Consequently X has 27 · 27 = 729 = 27² elements. "
                            + "Reindexing by the coordinate equivalence and using additivity of the angle map transfers the moment identity to design2(X), and transfers the exponential overlap calculation to mubOverlap(X). "
                            + "The zero matrix M₀ with zero linear term gives the zero phase function in X.")),
                    Paragraph(Text(
                        "Finally, suppose an additive subgroup had carrier X. It would contain the phase functions with parameters (1,0) and (3,0), hence their sum. "
                            + "That sum would be a phase function with some parameters (i,b). Injectivity of the angle map would identify its polynomial with xᵀ(M₁ + M₃)x. "
                            + "Uniqueness of symmetric quadratic and linear coefficients would force Mᵢ = M₁ + M₃, contradicting the finite matrix calculation. "
                            + "Thus X has no such subgroup carrier. Applying the universal assertion to d = 27 and this X contradicts that fact. "
                            + "The conclusion concerns these identity-containing representatives; it makes no assertion about whether a different choice of anchoring of a complete set of mutually unbiased bases yields a group, or about dimension six."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("iosue-mooney-ehrenberg-gorshkov-2024-projective-toric-design-subgroup-conjecture"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("projective-toric-nongroup-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DesignFormula()
    {
        Formula moments = And(
            Imp(PairAgreement(), Equal(MomentSum(), NatCast(Card(), Complexes()))),
            Imp(Not(PairAgreement()), Equal(MomentSum(), Typed(D(0), Complexes()))));
        Formula indices = All("a₁", FinOf(V("d")), All("a₂", FinOf(V("d")),
            All("b₁", FinOf(V("d")), All("b₂", FinOf(V("d")), moments))));
        return PhaseSetBinders(Equivalence(LocalCall("design2", V("X")), indices));
    }

    private static Formula OverlapFormula()
    {
        Formula values = Or(Equal(OverlapSquare(), Typed(D(0), Reals())),
            Equal(OverlapSquare(), NatCast(V("d"), Reals())));
        Formula theta = All("θ", Phases(), Imp(Member(V("θ"), V("X")),
            Imp(NotEqual(V("φ"), V("θ")), values)));
        Formula phases = All("φ", Phases(), Imp(Member(V("φ"), V("X")), theta));
        return PhaseSetBinders(Equivalence(LocalCall("mubOverlap", V("X")), phases));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"), ClaimProposition());

    private static Formula ClaimProposition()
    {
        Formula subgroup = Some("H", At(Qualified("AddSubgroup"), Phases()),
            Equal(SetCast(V("H")), SetCast(V("X"))));
        Formula zero = At(Qualified("Function", "const"), FinOf(V("d")), Typed(D(0), Angles()));
        Formula conditions = Imp(Equal(Card(), new Formula.Power(V("d"), D(2))),
            Imp(LocalCall("design2", V("X")), Imp(LocalCall("mubOverlap", V("X")),
                Imp(Member(zero, V("X")), subgroup))));
        Formula anchored = All("φ", Phases(), Imp(Member(V("φ"), V("X")),
            Equal(At(V("φ"), Typed(D(0), FinOf(V("d")))), Typed(D(0), Angles()))));
        return All("d", Naturals(), Imp(Less(Typed(D(0), Naturals()), V("d")),
            All("X", At(Qualified("Finset"), Phases()), Imp(anchored, conditions))));
    }

    private static Formula PairAgreement() => Or(
        And(Equal(V("a₁"), V("b₁")), Equal(V("a₂"), V("b₂"))),
        And(Equal(V("a₁"), V("b₂")), Equal(V("a₂"), V("b₁"))));

    private static Formula MomentSum() => Seq(
        new Formula.Subscript(Sum, Seq(V("φ"), Sp, InMacro, Sp, V("X"))), Sp,
        Parenthesized(CircleCast(Subtract(Subtract(
            Add(At(V("φ"), V("a₁")), At(V("φ"), V("a₂"))), At(V("φ"), V("b₁"))), At(V("φ"), V("b₂"))))));

    private static Formula OverlapSquare() => new Formula.Power(new Formula.Norm(
        Seq(new Formula.Subscript(Sum, Typed(V("j"), FinOf(V("d")))), Sp,
            Parenthesized(CircleCast(Subtract(At(V("φ"), V("j")), At(V("θ"), V("j"))))))), D(2));

    private static Formula PhaseSetBinders(Formula body) => All("d", Naturals(),
        All("X", At(Qualified("Finset"), Phases()), body));
    private static Formula CircleCast(Formula angle) => Typed(
        At(Qualified("Subtype", "val"), At(Qualified("Real", "Angle", "toCircle"), angle)), Complexes());
    private static Formula NatCast(Formula value, Formula type) => Typed(At(Qualified("Nat", "cast"), value), type);
    private static Formula SetCast(Formula value) => Typed(At(Qualified("SetLike", "coe"), value), At(Qualified("Set"), Phases()));
    private static Formula Card() => At(Qualified("Finset", "card"), V("X"));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Angles() => Qualified("Real", "Angle");
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Phases() => Parenthesized(new Formula.TypeArrow(FinOf(V("d")), Angles()));
    private static Formula V(string name) => name switch
    {
        "φ" => Varphi,
        "θ" => Theta,
        "a₁" => new Formula.Subscript(F.Id("a"), D(1)),
        "a₂" => new Formula.Subscript(F.Id("a"), D(2)),
        "b₁" => new Formula.Subscript(F.Id("b"), D(1)),
        "b₂" => new Formula.Subscript(F.Id("b"), D(2)),
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
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements", "ProjectiveToricDesignNonGroup", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
}
