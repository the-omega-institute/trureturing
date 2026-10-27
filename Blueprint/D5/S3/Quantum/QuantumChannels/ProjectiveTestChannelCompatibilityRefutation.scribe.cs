using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ProjectiveTestChannelCompatibilityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/zhangnechita2022fisherchannelincompatibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every pair of projective tests is compatible for a qubit channel that has no joint extension with itself.",
        H("Projective tests do not characterize channel compatibility"),
        Blocks(
            Node("basis-povm", "basisPOVM", "The adjoint image of a basis measurement", BasisPOVMFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The columns of the unitary matrix U form an orthonormal basis. For each i, apply the trace dual "
                    + "of the complex linear map φ to the rank-one projector onto column i. "
                    + "These are the projective-test effects in article.tex, lines 239-241 and 263-264. "
                    + "The definition applies to every complex linear matrix map; complete positivity and trace preservation "
                    + "are imposed separately when these effects are used as a POVM."),
            Node("channel-compatible", "ChannelCompatible", "A joint channel with two prescribed marginals", ChannelCompatibleFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A joint completely positive trace-preserving map sends an input matrix to a matrix on the product "
                    + "of the two output spaces. Tracing out the right output gives φ, and tracing out the left output gives ψ, "
                    + "on every complex input matrix. This is the equal-output-dimension case of the channel compatibility "
                    + "definition in article.tex, lines 138-146. The predicate requires the joint map to be a channel; "
                    + "it places no separate channel hypotheses on φ and ψ."),
            Node("claim", "claim", "The proposed converse from projective tests", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For every natural dimension d and every two completely positive trace-preserving maps φ and ψ, "
                    + "suppose that every pair of unitary bases gives compatible adjoint-image POVMs. "
                    + "Compatibility of POVMs means that a positive normalized family on the product outcome set "
                    + "has the two given families as its marginals, as in article.tex, lines 192-199. "
                    + "The assertion is that φ and ψ must then have a joint channel. "
                    + "This expresses the conjecture in article.tex, lines 261-266, using unitaries to parameterize bases. "
                    + "The displayed quantifier also includes dimension zero; the counterexample has dimension two."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A depolarizing qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Consider the qubit map φ(X) = (7/10)X + (3/20)tr(X)I. "
                            + "Its Pauli representation has probabilities 31/40, 3/40, 3/40 and 3/40. "
                            + "They are nonnegative and sum to one, so φ is completely positive and trace preserving. "
                            + "Cyclicity of the trace pairing shows that its trace dual equals φ.")),
                    Paragraph(Text(
                        "For arbitrary unitary bases U and V, let Eₐ and Fᵦ be their rank-one projectors. "
                            + "Each projector is Hermitian, has trace one and squares to itself; each pair sums to I. "
                            + "Thus Aₐ = 2Eₐ − I and Bᵦ = 2Fᵦ − I are traceless Hermitian matrices that square to I, "
                            + "and each centered pair sums to zero. Any two traceless two-by-two matrices A and B satisfy "
                            + "AB + BA = tr(AB)I, by expanding their entries and eliminating the second diagonal entries.")),
                    Paragraph(Text(
                        "Define the four joint effects Gₐᵦ = ((1 + (49/200)tr(AₐBᵦ))I + (7/10)(Aₐ + Bᵦ))/4. "
                            + "To prove positivity, fix a and b and write A = Aₐ, B = Bᵦ and K = A + B. "
                            + "The anticommutator identity gives K² = (2 + tr(AB))I. Since K is Hermitian, K² is positive semidefinite; "
                            + "a diagonal entry therefore shows that tr(AB) is real and at least −2. Put τ = Re(tr(AB)), "
                            + "α = 1 + (49/200)τ and c = 1/50 + (2401/40000)τ². Then α and c are strictly positive, "
                            + "and c = α² − (49/100)(2 + τ). For the Hermitian matrix H = αI + (7/10)K, "
                            + "expansion gives H*H + cI = 2αH, where the star denotes conjugate transpose. "
                            + "Consequently H = (H*H + cI)/(2α) is positive semidefinite, and Gₐᵦ = H/4 is positive semidefinite.")),
                    Paragraph(Text(
                        "Summing over b cancels the centered B terms and the mixed trace terms, leaving "
                            + "sum over b of Gₐᵦ = φ(Eₐ). Cyclicity of trace and exchange of A and B give "
                            + "sum over a of Gₐᵦ = φ(Fᵦ). Summing again gives I. "
                            + "The marginals are themselves positive semidefinite and normalized, so the four effects form "
                            + "a joint POVM for the two adjoint-image measurements. This holds for every U and V.")),
                    Paragraph(Text(
                        "Now suppose that a joint channel J for φ and itself exists. Order its Choi indices as ((a,b),r), "
                            + "with a and b the two output indices and r the reference index. Its normalized Choi matrix R "
                            + "has entries R(((a,b),r),((c,d),s)) = J(|r><s|)((a,b),(c,d))/2. "
                            + "Complete positivity makes R positive semidefinite. Trace preservation gives "
                            + "tr(R) = (tr(J(|0><0|)) + tr(J(|1><1|)))/2 = 1.")),
                    Paragraph(Text(
                        "Let S be the Bell projection on the first output and reference, tensored with the identity "
                            + "on the second output, and let T be the corresponding projection for the second output and reference. "
                            + "The Bell vector is (|00> + |11>)/√2. Expanding the two partial-trace equalities on the matrix units "
                            + "gives tr(RS) = (sum over r,s,b of J(|r><s|)((r,b),(s,b)))/4 "
                            + "= (sum over r,s of φ(|r><s|)(r,s))/4 = 31/40. "
                            + "The other marginal gives tr(RT) = 31/40 in the same way.")),
                    Paragraph(Text(
                        "The matrix (3/2)I − S − T is positive semidefinite by an explicit Gram decomposition. "
                            + "Write eₐᵦᵣ for the coordinate row with index ((a,b),r). Let C have the four rows "
                            + "e₀₀₀ − e₀₁₁ − e₁₀₁, e₀₁₁ − e₁₀₁, e₁₁₁ − e₀₁₀ − e₁₀₀ and e₀₁₀ − e₁₀₀. "
                            + "Let D be diagonal with entry 3/2 at ((0,0),1) and ((1,1),0), and zero elsewhere. "
                            + "Entrywise expansion gives (3/2)I − S − T = C*C/2 + D. "
                            + "Both summands are positive semidefinite.")),
                    Paragraph(Text(
                        "The trace of the product of two positive semidefinite matrices is nonnegative. Applying this to R "
                            + "and (3/2)I − S − T gives 0 ≤ (3/2)tr(R) − tr(RS) − tr(RT) "
                            + "= 3/2 − 31/40 − 31/40 = −1/20, a contradiction. Thus φ has no joint channel with itself. "
                            + "Applying claim in dimension two to φ twice would provide just such a joint channel, "
                            + "because both maps are channels and all their projective-test pairs have the joint POVMs above. "
                            + "Therefore claim is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-nechita-2022-projective-test-channel-compatibility-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula BasisPOVMFormula() =>
        All("d", Naturals(), All("φ", MapType(FinD(), FinD()), All("U", UnitaryType(),
            Equal(Typed(LocalCall("basisPOVM", X("φ"), X("U")), Arrow(FinD(), MatrixType())),
                LambdaOf("i", FinD(), At(CoerceFunction(At(MapMember("dual"), X("φ"))),
                    At(Qualified("D5", "S3", "Quantum", "Decoherence", "DephasingTwoClassicalityBlockRefutation",
                        "measurementProjector"), X("U"), X("i"))))))));

    private static Formula ChannelCompatibleFormula()
    {
        Formula first = All("X", MatrixType(), Equal(
            At(PartialTrace("partialTraceRight"), At(CoerceFunction(X("J")), X("X"))),
            At(CoerceFunction(X("φ")), X("X"))));
        Formula second = All("X", MatrixType(), Equal(
            At(PartialTrace("partialTraceLeft"), At(CoerceFunction(X("J")), X("X"))),
            At(CoerceFunction(X("ψ")), X("X"))));
        Formula joint = Some("J", MapType(FinD(), Product(FinD(), FinD())),
            And(CPTP(X("J")), And(first, second)));
        return All("d", Naturals(), All("φ", MapType(FinD(), FinD()), All("ψ", MapType(FinD(), FinD()),
            Iff(LocalCall("ChannelCompatible", X("φ"), X("ψ")), joint))));
    }

    private static Formula ClaimFormula()
    {
        Formula tests = All("U", UnitaryType(), All("V", UnitaryType(),
            At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "ConcealmentKernelNecessityRefutation", "Compatible"),
                LocalCall("basisPOVM", X("φ"), X("U")), LocalCall("basisPOVM", X("ψ"), X("V")))));
        Formula statement = All("d", Naturals(), All("φ", MapType(FinD(), FinD()), All("ψ", MapType(FinD(), FinD()),
            Arrow(CPTP(X("φ")), Arrow(CPTP(X("ψ")), Arrow(tests, LocalCall("ChannelCompatible", X("φ"), X("ψ"))))))));
        return Iff(Local("claim"), statement);
    }

    private static Formula CPTP(Formula map) =>
        At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "ChannelAssemblageLOSRRefutation", "IsCPTP"), map);
    private static Formula PartialTrace(string name) =>
        Qualified("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", name);
    private static Formula MapMember(string name) =>
        Qualified("D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap", name);
    private static Formula MapType(Formula input, Formula output) =>
        At(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap"),
            input, output, Complexes());
    private static Formula UnitaryType() =>
        At(Qualified("Subtype"), LambdaOf("x", MatrixType(),
            new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf,
                At(Qualified("Matrix", "unitaryGroup"), FinD(), Complexes()))));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinD(), FinD(), Complexes());
    private static Formula FinD() => At(Qualified("Fin"), X("d"));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "QuantumChannels", "ProjectiveTestChannelCompatibilityRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "φ" => Phi,
        "ψ" => Psi,
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula CoerceFunction(Formula value) => Parenthesized(At(Qualified("DFunLike", "coe"), value));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
