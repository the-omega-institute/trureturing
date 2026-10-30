using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ErrorDisturbanceEndpointRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/zhouwuchau2016errordisturbance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational three-dimensional measurement has overall error below both endpoint quantities.",
        H("Error and disturbance below the endpoint minimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sum-projectors"),
                DeclarationHandle.Create(Prefix + "sum_projectors"),
                H("Unitary basis projectors resolve the identity"),
                StatementSource.FromAuthor(Disp(All("d", Naturals(), All("a", UnitaryType(),
                    Equal(Seq(new Formula.Subscript(Sum, Typed(X("i"), FinType())), Sp,
                        Projector(X("a"), X("i"))), Typed(D(1), MatrixType())))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rank-one projectors onto the columns of any unitary matrix sum to the identity."))),
                DescribeRole.Theorem),
            Definition("error-at", "errorAt", "State-dependent labeled error", ErrorAtFormula(),
                "For a complex matrix ρ, take the supremum over the labeled outcomes i of the absolute real part "
                    + "of the trace against the difference of the two rank-one projectors. For a density matrix "
                    + "this is the infinity distance between the two outcome distributions. The bases a and c "
                    + "are the columns of unitary matrices. This is the error of new_912arxiv.tex, lines 182–197. "
                    + "The definition itself is given for every matrix ρ and every natural dimension d.", true),
            Definition("disturbance-at", "disturbanceAt", "State-dependent disturbance", DisturbanceAtFormula(),
                "For outcome j of b, subtract from its projector its image under the unread projective "
                    + "measurement in c, and take the absolute real part of its expectation in ρ. The supremum "
                    + "over j is the infinity distance between the b distributions before and after that measurement "
                    + "when ρ is a density matrix. Here unreadState sends an observable X to the sum of QₖXQₖ "
                    + "over the projectors Qₖ of c. This expresses new_912arxiv.tex, lines 175–197, in terms of observables.", true),
            Definition("overall-error", "overallError", "Overall error in one common state", OverallErrorFormula(),
                "Take the real supremum of the sum of labeled error and disturbance over density matrices ρ. "
                    + "Both summands use the same ρ; the expression is not the sum of two separately optimized "
                    + "quantities. This is the overall error defined in new_912arxiv.tex, lines 215–223.", true),
            Definition("error", "error", "State-independent labeled error", ErrorFormula(),
                "The state-independent labeled error is the supremum of errorAt over positive semidefinite "
                    + "complex matrices of trace one. The labels of the columns of a and c are kept fixed. "
                    + "This is the state-independent error of new_912arxiv.tex, lines 200–204, with the maximum "
                    + "written as a real supremum.", true),
            Definition("disturbance", "disturbance", "State-independent disturbance", DisturbanceFormula(),
                "The state-independent disturbance is the supremum of disturbanceAt over positive semidefinite "
                    + "complex matrices of trace one. This is new_912arxiv.tex, lines 200–209, with the maximum "
                    + "written as a real supremum. No lower bound on d is imposed in these definitions.", true),
            Definition("relabel", "relabel", "Permuting the outcome labels", RelabelFormula(),
                "The permutation π reorders the columns of b while the row indices are fixed. Thus column i "
                    + "of the relabeled basis is column π(i) of b. Reindexing rows and columns by equivalences "
                    + "preserves unitarity, so the resulting matrix again defines an element of the unitary group. "
                    + "Subtype.val specifies the underlying matrix; its unitarity proof does not affect the value.", false),
            Definition("relaxed-error", "relaxedError", "Error with freely relabeled outcomes", RelaxedErrorFormula(),
                "Take the infimum of the labeled error over every permutation π of Fin d. Since this permutation "
                    + "type is finite and nonempty, it is a minimum. It implements the disregard of outcome labels "
                    + "in new_912arxiv.tex, lines 614–620.", true),
            Definition("claim", "claim", "The proposed lower bound on overall error", ClaimFormula(),
                "For every natural d at least two and every three unitary measurement bases a, c and b, "
                    + "the proposed inequality bounds overallError from below by the minimum of the relaxed "
                    + "error between a and b and the disturbance of b caused by a. This is the second inequality "
                    + "of Conjecture 3 in new_912arxiv.tex, lines 623–639, with only the endpoint error relaxed "
                    + "over outcome labels. It asserts neither the first inequality nor the equality conditions.", false),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A rational counterexample in dimension three"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take a to be the standard basis in dimension three. Let C be the unitary whose rows "
                            + "are (312/313, −25/313, 0), (25/313, 312/313, 0), (0, 0, 1). Let B have rows "
                            + "(32976/33205, −3757/33205, −1020/33205), "
                            + "(3893/33205, 31824/33205, 8640/33205), (0, −8700/33205, 32045/33205). "
                            + "Their products with their conjugate transposes are the identity, by exact rational arithmetic. "
                            + "Write Pᵢ, Qᵢ and Rⱼ for the rank-one projectors of a, C and B, respectively. "
                            + "Set Eᵢ = Pᵢ − Qᵢ and Dⱼ = Rⱼ − ∑ₖ QₖRⱼQₖ.")),
                    Paragraph(Text(
                        "Each projector entry is the product of a column entry and the conjugate of another "
                            + "entry in the same column. Expanding these products gives exact rational tables for Eᵢ "
                            + "and Dⱼ. In particular E₁ = −E₀ and E₂ = 0, with indices starting at zero. "
                            + "Put s = 71/250. For each j in Fin 3 and each of the four sign pairs ε, δ in {1, −1}, "
                            + "the matrix sI − (εE₀ + δDⱼ) has an exact factorization L diag(q) Lᴴ with all three "
                            + "entries of q nonnegative. The diagonal matrix is positive semidefinite, and conjugation "
                            + "by L preserves that property. These twelve factorizations therefore establish positivity. "
                            + "The identity E₁ = −E₀ supplies the same bounds at i = 1 by reversing ε. At i = 2, "
                            + "average the two inequalities for ε = 1 and ε = −1 to cancel E₀.")),
                    Paragraph(Text(
                        "For any density matrix ρ, positivity of sI − (εEᵢ + δDⱼ) implies "
                            + "ε Re tr(ρEᵢ) + δ Re tr(ρDⱼ) ≤ s, using positivity of trace products and tr ρ = 1. "
                            + "The finite outcome suprema are attained. Choose maximizing indices i and j and choose "
                            + "each sign according to the sign of its real expectation. Their sum of absolute values "
                            + "is at most s, so errorAt ρ a C + disturbanceAt ρ C B ≤ s for every density matrix. "
                            + "For a nonzero vector x with squared norm n, xxᴴ/n is positive semidefinite and has "
                            + "trace one, by normalization of its trace. Density matrices in dimension three are "
                            + "nonempty; taking the supremum gives overallError a C B ≤ 71/250.")),
                    Paragraph(Text(
                        "To justify the endpoint suprema, note that the projectors of any unitary basis sum to I. "
                            + "Their complements are sums of the remaining positive semidefinite projectors. "
                            + "For any two effects X and Y with X, Y, I − X and I − Y positive semidefinite, "
                            + "both real expectations in a density matrix lie in [0, 1]; hence "
                            + "|Re tr(ρ(X − Y))| ≤ 1. Measurement in the standard basis sends Rⱼ to its diagonal "
                            + "matrix of diagonal entries. That matrix and its complement are positive semidefinite, "
                            + "by the corresponding diagonal inequalities for Rⱼ and I − Rⱼ. Consequently the "
                            + "sets defining disturbance a B and every error a (relabel B π) are bounded above by 1.")),
                    Paragraph(Text(
                        "Put r = 57/200. For x = (−5, 11, −10), its squared norm is 246 and the pure state "
                            + "xxᴴ/246 is a density matrix. At outcome j = 1, the expectation of R₁ minus its "
                            + "diagonal part is exactly 2577721016/9041090605, which exceeds r. Its absolute value "
                            + "is therefore a lower bound on disturbanceAt in this state.")),
                    Paragraph(Text(
                        "For an arbitrary permutation π, split according to π(1). If π(1) = 0 or π(1) = 2, "
                            + "use x = (0, 1, 0), of squared norm 1. If π(1) = 1, use x = (−5, −16, −11), "
                            + "of squared norm 402. In each case xxᴴ divided by that squared norm is a density "
                            + "matrix. The real expectation differences at i = 1 are 20736/21025, "
                            + "42157045933/147744651350 and 41116897/44102881 when π(1) is 0, 1 and 2, "
                            + "respectively. All three exceed r, so the labeled error exceeds r.")),
                    Paragraph(Text(
                        "The preceding states and boundedness place disturbance a B and every error a (relabel B π) "
                            + "strictly above r. There are finitely many permutations, so their infimum, relaxedError a B, "
                            + "also exceeds r. Thus the minimum of the two endpoint quantities is strictly greater "
                            + "than 57/200, whereas overallError a C B ≤ 71/250 < 57/200. Applying the proposed "
                            + "inequality at d = 3 to a, C and B gives a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhou-wu-chau-2016-error-disturbance-endpoint-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula,
        string prose, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ErrorAtFormula()
    {
        Formula difference = Sub(Projector(X("a"), X("i")), Projector(X("c"), X("i")));
        return All("d", Naturals(), All("ρ", MatrixType(), All("a", UnitaryType(), All("c", UnitaryType(),
            Equal(Typed(Call("errorAt", X("ρ"), X("a"), X("c")), Reals()),
                IndexedSup("i", Expectation(difference)))))));
    }

    private static Formula DisturbanceAtFormula()
    {
        Formula target = Projector(X("b"), X("j"));
        Formula unread = At(Qualified("D5", "S3", "Observer", "Conditioning", "unreadState"),
            At(ProjectorName(), X("c")), target);
        return All("d", Naturals(), All("ρ", MatrixType(), All("c", UnitaryType(), All("b", UnitaryType(),
            Equal(Typed(Call("disturbanceAt", X("ρ"), X("c"), X("b")), Reals()),
                IndexedSup("j", Expectation(Sub(target, unread))))))));
    }

    private static Formula OverallErrorFormula() => All("d", Naturals(),
        All("a", UnitaryType(), All("c", UnitaryType(), All("b", UnitaryType(),
            Equal(Typed(Call("overallError", X("a"), X("c"), X("b")), Reals()),
                StateSup(Add(Call("errorAt", X("ρ"), X("a"), X("c")),
                    Call("disturbanceAt", X("ρ"), X("c"), X("b")))))))));

    private static Formula ErrorFormula() => All("d", Naturals(),
        All("a", UnitaryType(), All("c", UnitaryType(),
            Equal(Typed(Call("error", X("a"), X("c")), Reals()),
                StateSup(Call("errorAt", X("ρ"), X("a"), X("c")))))));

    private static Formula DisturbanceFormula() => All("d", Naturals(),
        All("c", UnitaryType(), All("b", UnitaryType(),
            Equal(Typed(Call("disturbance", X("c"), X("b")), Reals()),
                StateSup(Call("disturbanceAt", X("ρ"), X("c"), X("b")))))));

    private static Formula RelabelFormula()
    {
        Formula value = At(Qualified("Subtype", "val"), X("b"));
        Formula reordered = At(Qualified("Matrix", "submatrix"), value,
            At(Qualified("Equiv", "toFun"), At(Qualified("Equiv", "refl"), FinType())),
            At(Qualified("Equiv", "toFun"), X("π")));
        return All("d", Naturals(), All("b", UnitaryType(), All("π", PermType(),
            Equal(Typed(At(Qualified("Subtype", "val"),
                Typed(Call("relabel", X("b"), X("π")), UnitaryType())), MatrixType()), reordered))));
    }

    private static Formula RelaxedErrorFormula() => All("d", Naturals(),
        All("a", UnitaryType(), All("b", UnitaryType(),
            Equal(Typed(Call("relaxedError", X("a"), X("b")), Reals()),
                At(Qualified("iInf"), LambdaOf("π", PermType(),
                    Call("error", X("a"), Call("relabel", X("b"), X("π")))))))));

    private static Formula ClaimFormula()
    {
        Formula endpoint = At(Qualified("min"), Call("relaxedError", X("a"), X("b")),
            Call("disturbance", X("a"), X("b")));
        Formula inequality = LE(endpoint, Call("overallError", X("a"), X("c"), X("b")));
        return Equal(Typed(Local("claim"), Qualified("Prop")), Parenthesized(
            All("d", Naturals(), Arrow(LE(Typed(D(2), Naturals()), X("d")),
                All("a", UnitaryType(), All("c", UnitaryType(), All("b", UnitaryType(), inequality)))))));
    }

    private static Formula StateSup(Formula expression) => At(Qualified("sSup"),
        Seq(OpenBrace, Typed(X("t"), Reals()), Sp, Mid, Sp,
            Some("ρ", MatrixType(), And(
                At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), X("ρ")),
                Equal(X("t"), expression))), CloseBrace));
    private static Formula IndexedSup(string name, Formula expression) =>
        At(Qualified("iSup"), LambdaOf(name, FinType(), expression));
    private static Formula Expectation(Formula observable) => new Formula.Absolute(
        At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"), Mul(X("ρ"), observable))));
    private static Formula ProjectorName() => Qualified("D5", "S3", "Quantum", "Decoherence",
        "DephasingTwoClassicalityBlockRefutation", "measurementProjector");
    private static Formula Projector(Formula basis, Formula index) => At(ProjectorName(), basis, index);
    private static Formula MatrixType() => At(Qualified("Matrix"), FinType(), FinType(), Complexes());
    private static Formula UnitaryType() => At(Qualified("CoeSort", "coe"),
        At(Qualified("Matrix", "unitaryGroup"), FinType(), Complexes()));
    private static Formula PermType() => At(Qualified("Equiv", "Perm"), FinType());
    private static Formula FinType() => At(Qualified("Fin"), X("d"));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "ErrorDisturbanceEndpointRefutation", name);
    private static Formula Call(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => name switch { "ρ" => Rho, "π" => Pi, _ => F.Id(name) };
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
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
}
