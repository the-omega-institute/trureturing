// Source-owning exposition for the prescribed-label deletion distance module.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class PrescribedDeletionDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/PrescribedDeletionDistance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual k-label circular deletion code has minimum distance k-2; "
            + "uniform recovery from t whole-readout errors and e known erasures holds exactly when 2t+e<k-2.",
        H("Distance of Prescribed Circular Deletions"), Blocks(
            Paragraph(Text("Status: canonical source in the research integration. The two theorems retain the accepted "
                + "mathematical source; exact decoding applications remain transient checks. Per-declaration "
                + "registration audit is unfinished, and this source integration makes no registration or delivery claim.")),
            Paragraph(Text("Let T be any label type with decidable equality, A a finite support of size n>=4, "
                + "and J a subset of A with k=|J|>=3. States are SupportedCircle A: nodup oriented circles, "
                + "identified only up to rotation. The output at x is the actual delete x C. "
                + "ReadoutAlphabet A x is exactly the image of that deletion map, encoded as a subtype of Cycle T. "
                + "The word is a dependent tuple indexed by J. Equality is tested only within a fixed coordinate. "
                + "No assumption that T is finite is used. Feasibility requires k<=n.")),
            Describe.Lean(DescribeId.Create("exact-prescribed-deletion-distance"),
                DeclarationHandle.Create(Prefix + "exact_prescribed_distance"),
                H("The Exact Minimum Distance Is k-2"),
                StatementSource.FromAuthor(DistanceFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If two distinct supported circles agreed at three distinct labels of J, "
                    + "ThreeSpecifiedDeletions.reconstruct_three would identify them. Thus their agreement set "
                    + "has at most two elements. The agreement and disagreement sets partition J, giving distance "
                    + "at least k-2. Choose distinct a,b in J and apply the existing two_deletions_insufficient theorem. "
                    + "Its actual supported collision agrees at a and b. A third agreeing label is impossible by "
                    + "reconstruct_three, so this pair has exactly two agreements and distance k-2. "
                    + "Both existing proofs are reused without reconstruction or finite enumeration. "
                    + "The new finite-set bound and attainment calculation are the substantive missing composition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ambiguity-at-failed-budget"),
                DeclarationHandle.Create(Prefix + "ambiguity_of_failed_budget"),
                H("A Failed Budget Has an Actual Legal Ambiguity Witness"),
                StatementSource.FromAuthor(SharpnessFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ReadoutSection A is the dependent function type assigning an actual "
                    + "deletion-image value at every label. Only its restriction to J outside E is received; "
                    + "the section fills unused coordinates with C's own readout. errorCount counts labels "
                    + "in J outside E where the section value differs from the given state's deletion. "
                    + "The proof chooses an attaining pair, erases min(e,k-2) disagreements, and partitions "
                    + "the remaining disagreements into two error sets. At each coordinate it constructs "
                    + "a subtype value with witness C or D. Exact filter identities identify the two error "
                    + "sets, proving the bounds without requiring any third symbol in any alphabet."))),
                DescribeRole.Theorem),
            Paragraph(Text("For decoding, choose a bijection i -> x_i from Fin k to J and embed each "
                + "ReadoutAlphabet A x_i into Cycle T by subtype value. This preserves coordinate equality and "
                + "hence Hamming distance. Let Ccode be the range of the actual deletion-word map. "
                + "Apply ErrorErasureUniqueDecoding.error_erasure_unique_decoding with its alphabet alpha=Cycle T, "
                + "length n=k, distance d=k-2, error parameter e=t and erasure parameter s=e. "
                + "Its erased finset is the reindexed known erased-label set. A received value at an unerased "
                + "label must belong to ReadoutAlphabet A x_i; erased coordinates may be filled with the true "
                + "word for this existence/uniqueness argument, because those values are never compared. "
                + "The theorem gives a unique codeword under 2t+e<k-2. Three-label reconstruction transfers "
                + "codeword uniqueness to circle uniqueness. This is an exact application of an existing "
                + "generic theorem and should be checked transiently, not retained as a bind-only declaration.")),
            Paragraph(Text("Sharpness uses the same actual attaining pair C,D. Let Delta be its k-2 "
                + "disagreeing labels. If 2t+e>=k-2, erase min(e,k-2) labels in Delta. Partition the remaining "
                + "q<=2t labels into P,Q of sizes at most t. At labels in P receive D's readout and elsewhere "
                + "receive C's readout. The received tuple differs from C on P and from D on Q. "
                + "Both are compatible; no decoder can recover the transmitted object uniformly. "
                + "Every received coordinate is an actual same-label deletion output of C or D and so belongs "
                + "to its stipulated alphabet. This construction also covers equality, zero errors, zero erasures "
                + "and erasure budgets greater than k by using at most the budget. "
                + "ArbitraryErrorCorrectionCapacity contains a related split-disagreement construction, but its "
                + "public capacity theorem assumes residue-code moduli and cannot be applied to circular words.")),
            Paragraph(Text("The exact minimum prescribed observation budget is 2t+e+3 when that number is "
                + "at most n; otherwise no choice of distinct deletion labels can provide the uniform guarantee. "
                + "Without erasures the guaranteed error radius is floor((k-3)/2), using the existing "
                + "UniqueDecodingRadius.unique_decoding_radius theorem with d=k-2. With no errors, at most "
                + "k-3 erasures are guaranteed. Boundary k=3 has distance one and guarantees only exact readouts.")),
            Paragraph(Text("For a particular known erasure set E and received partial word r, the exact "
                + "criterion is that the set of supported circles differing from r at at most t unerased "
                + "labels is a singleton. The global threshold concerns every state and every admissible noise "
                + "pattern; its failure supplies an ambiguous instance, not ambiguity of each received word. "
                + "For a fixed circle C and E, define its local punctured separation as the minimum, over D!=C, "
                + "of the number of their disagreeing labels outside E. Every radius-t corruption of C is "
                + "uniquely compatible precisely when twice t is smaller than that local separation. "
                + "These are exact mathematical criteria, not a classification of all local separations. "
                + "No claim concerns character edits, mislabeled coordinates, unlabeled decks, marginal laws, "
                + "running time, sample complexity, adaptive sampling or literature novelty.")))));

    private static Formula DistanceFormula()
    {
        Formula t=F.Id("T"), a=F.Id("A"), j=F.Id("J"), c=F.Id("C"), d=F.Id("D"), x=F.Id("x");
        Formula states=Call("SupportedCircle",a);
        Formula k=Call("card",j);
        Formula distance=Call("readoutDistance",j,c,d);
        Formula bound=Seq(k,Sp,Minus,Sp,D(2));
        Formula lower=All("C",states,All("D",states,
            Imp(Ne(c,d),Le(bound,distance))));
        Formula agreeing=Seq(OpenBrace,x,Sp,InMacro,Sp,j,Sp,Mid,Sp,
            Call("delete",x,c),Sp,F.Eq,Sp,Call("delete",x,d),CloseBrace);
        Formula attaining=Ex("C",states,Ex("D",states,
            And(Ne(c,d),And(Eq(Call("card",agreeing),D(2)),Eq(distance,bound)))));
        Formula hypotheses=And(Le(D(4),Call("card",a)),
            And(Call("Subset",j,a),Le(D(3),k)));
        return Disp(All("T",Call("Type"),Seq(OpenBracket,Call("DecidableEq",t),CloseBracket,Sp,
            All("A",Call("Finset",t),All("J",Call("Finset",t),
                Imp(hypotheses,And(lower,attaining)))))));
    }

    private static Formula SharpnessFormula()
    {
        Formula a=F.Id("A"),j=F.Id("J"),t=F.Id("t"),e=F.Id("e");
        Formula c=F.Id("C"),d=F.Id("D"),erased=F.Id("E"),r=F.Id("r"),type=F.Id("T");
        Formula bound=Seq(Call("card",j),Sp,Minus,Sp,D(2));
        Formula budget=Seq(D(2),Sp,Times,Sp,t,Sp,Plus,Sp,e);
        Formula hypotheses=And(Le(D(4),Call("card",a)),And(Call("Subset",j,a),
            And(Le(D(3),Call("card",j)),Le(bound,budget))));
        Formula counts=And(Le(Call("errorCount",j,erased,r,c),t),
            Le(Call("errorCount",j,erased,r,d),t));
        Formula witness=Ex("C",Call("SupportedCircle",a),Ex("D",Call("SupportedCircle",a),
            And(Ne(c,d),Ex("E",Call("Finset",type),
                And(Call("Subset",erased,j),And(Le(Call("card",erased),e),
                    Ex("r",Call("ReadoutSection",a),counts)))))));
        return Disp(All("T",Call("Type"),Seq(OpenBracket,Call("DecidableEq",type),CloseBracket,Sp,
            All("A",Call("Finset",type),All("J",Call("Finset",type),
                All("t",Call("Nat"),All("e",Call("Nat"),Imp(hypotheses,witness))))))));
    }

    private static Formula Call(string name,params Formula[] args)=>args.Length==0
        ?new Formula.NamedConstant(FormulaIdentifier.Create(name))
        :new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)),[..args]);
    private static Formula All(string n,Formula domain,Formula body)=>new Formula.Bind(
        FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),domain,body);
    private static Formula Ex(string n,Formula domain,Formula body)=>new Formula.Bind(
        FormulaQuantifier.Exists,FormulaIdentifier.Create(n),domain,body);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>new Formula.Not(Seq(Open,Eq(a,b),Close));
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(Seq(Open,a,Close),FormulaLogicOperator.And,Seq(Open,b,Close));
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(Seq(Open,a,Close),FormulaLogicOperator.Implies,Seq(Open,b,Close));
}
