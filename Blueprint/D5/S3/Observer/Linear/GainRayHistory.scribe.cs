using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRayHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal M and J acquisition with arbitrary actual-history decisions", H("Literal M and J acquisition with arbitrary actual-history decisions"), Blocks(
            Paragraph(Text("A chronological word is a list of Booleans: false is M=[0,1;1,1], and true is J=[0,1;1,0]. acquisition is the real cast of the integral chronological word. Its empty word is the identity. Appending an atom multiplies the cumulative matrix on the left by exactly that atom. This connects the real sensor directly to the integral word laws.")),
            Paragraph(Text("readAt W w i is gain(d,W.coeff)(i) times trace(acquisition(take i w) W.source), plus W.drift. readings W w restricts this expression to Fin(length(w)+1). Thus the identity read at clock zero is present, and every atom has exactly one immediately following read. The finite history contains the original clocks 0 through length(w). No reset, copied source, skipped read, extra sensor or clock renumbering is part of the protocol.")),
            Paragraph(Text("A Readout d w is a fixed real matrix with d+1 rows and length(w)+1 columns. Collinear allows an arbitrary real scalar, including zero. Succeeds requires a nonzero real scalar, of either sign, multiplying the whole coefficient vector. Zero output never counts as success.")),
            Paragraph(Text("A Protocol fixes a countable set of matrices for each word before observations. Its decide function takes the entire word and its entire real history and either chooses one next M or J, or stops with a member of that word's fixed palette. Empty, finite and countably infinite palettes are permitted. No continuity, measurability, computability or finite response alphabet is assumed.")),
            Paragraph(Text("Reaches is an inductive actual execution predicate. It starts with the initial read and extends only when decide selects the next atom from the already acquired history. Terminates also requires the stop decision to select its stated palette member. UniformlySuccessful P N requires on every original World d an actual terminating execution with at most N total reads whose selected matrix succeeds. Gain-only correctness is the nonzero scalar condition; complete-target recovery is a separate task.")),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayhistory-acquisition-append"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayHistory.acquisition_append"),
                H("Real and integral chronological acquisition agree"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every word w and Boolean a, acquisition(w++[a])=action(a) acquisition(w). This uses the chronological append conjunct of raw_word_signed_bound under the real ring homomorphism."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-pure-acquisition"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayHistory.acquisition_pure"),
                H("Literal repeated atoms are matrix powers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every Boolean a and natural n, acquisition of n repeated copies of a equals action(a) to the power n. The identity at n=0 and chronological append at n+1 give this native power interface for both M and J."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayhistory-identical-prefix-transfer"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayHistory.identical_prefix_transfer"),
                H("Actual prefixes transfer through arbitrary decisions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d, protocol P, worlds W and Wprime, and word w, if Reaches P W w and readings W w=readings Wprime w, then Reaches P Wprime w and P.decide w gives the same decision on these two histories. The proof restricts the final equal history to each prior word and inducts through the actual execution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayhistory-identical-prefix-firstm"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayHistory.identical_prefix_firstM"),
                H("The same first M is actually executed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every d,P,W,Wprime and natural n, suppose P actually reaches the word of n copies of J on W, the two worlds have identical readings on that word, and its next decision on W is M. Then P actually reaches J repeated n followed by M on Wprime. The transferred M is at original clock n+1. This includes n=0 and imposes no equality of subsequent histories or terminal words."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-terminal-extends-reached"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayHistory.terminal_extends_reached"),
                H("A terminal word extends every acquired prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every d, protocol P, world W, words p,w and member C of the fixed palette at w, Reaches P W p and Terminates P W w C imply that p is a prefix of w. Reached words of the same length are equal, by induction through their actual deterministic decisions. Every initial part of a reached word is reached. A terminal word cannot be shorter than another reached word, because its stop decision would then equal an action decision. Thus a forced M remains present in the terminal word supplied by a uniform read bound."))), DescribeRole.Theorem))));
}
