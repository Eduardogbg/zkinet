import Mathlib.Data.Finset.Basic

variable
  /- we'll usually use α for the node type's labels -/
  {α: Type} [DecidableEq α]
  /- we'll usually use β for the rule name's labels -/
  {β: Type} [DecidableEq β]

structure NodeContext (α : Type) where
  /-- a finite set of all node types for this context -/
  node_types: Finset α
  /-- maps a node type to its arity of positive polarity -/
  pos_ports: node_types → ℕ
  /-- maps a node type to its arity of negative polarity -/
  neg_ports: node_types → ℕ

/--
  an interaction net is a set of nodes and a wiring between their ports
  (one of the most obvious definitions we'll have)
-/
structure InteractionNet (ctx: NodeContext α) where
  /-- a finite set of indices for all of the net's nodes -/
  nodes: Finset ℕ
  /-- a mapping that associates each node to its respective type -/
  assign_node_type: nodes → ctx.node_types

  /-- dependent product type between a node and a index for one of its positive ports -/
  PosPort: Type := (n: nodes) × (Fin (ctx.pos_ports (assign_node_type n)))
  /-- dependent product type between a node and a index for one of its negative ports -/
  NegPort: Type := (n: nodes) × (Fin (ctx.neg_ports (assign_node_type n)))
  /-- a bijection wiring together all positive and negative ports in the net -/
  wiring: PosPort ≃ NegPort

/--
  an interaction rule describes how to patch a net when a given pair of node types
  (with opposite polarity for their principal ports) is interacting.
-/
structure InteractionRule (ctx: NodeContext α) where
  /-- the node type with positive principal port for this rule -/
  pos_node_type: ctx.node_types
  /-- the node type with negative principal port for this rule -/
  neg_node_type: ctx.node_types

  /-- asserts that the positive node type for this rule has a positive principal port (index 0) -/
  has_principal_pos: 0 < ctx.pos_ports pos_node_type
  /-- asserts that the positive node type for this rule has a negative principal port (index 0) -/
  has_principal_neg: 0 < ctx.neg_ports neg_node_type

  /-- a finite set of indices for all output nodes of this rule -/
  output_nodes: Finset ℕ
  /-- a mapping that associates each output node of the rule to its respective type -/
  o: output_nodes → ctx.node_types

  /--
    a disjoint sum of the types of ports to be interpreted as
    boundary ports of positive polarity of the rule. these are:
    1. the non-principal positive ports of the positive node
    2. all the positive ports of the negative node

    these are given as indices, and implicitly the first entry's ports
    should be shifted by 1, as 0 is the principal port and the
    first entry only has boundary non-pricipal ports.
  -/
  BoundPos: Type :=
    (Fin (ctx.pos_ports pos_node_type - 1))
    ⊕ (Fin (ctx.pos_ports neg_node_type))
  /--
    a disjoint sum of the types of ports to be interpreted as
    boundary ports of negative polarity of the rule. these are:
    1. the non-principal negative ports of the negative node
    2. all the negative ports of the positive node

    these are given as indices, and implicitly the first entry's ports
    should be shifted by 1, as 0 is the principal port and the
    first entry only has boundary non-pricipal ports.
  -/
  BoundNeg: Type :=
    (Fin (ctx.neg_ports neg_node_type - 1))
    ⊕ (Fin (ctx.neg_ports pos_node_type))

  /--
    the ports of output nodes of positive polarity, given as a product of a node's
    index and its positive ports indices.
  -/
  OutPos: Type := (n: output_nodes) × Fin (ctx.pos_ports (o n))
  /--
    the output ports of positive polarity, given as a product of a node's
    index and its negative ports indices.
  -/
  OutNeg: Type := (n: output_nodes) × Fin (ctx.neg_ports (o n))

  /--
    "a bijection i : B− + O+ → B+ + O− wiring each positive (output or boundary)
    port onto a negative (output or boundary) port.

    notice that negative boundary ports may be wired to negative output ports by i,
    and similarly for positive boundary ports and positive output ports. this is
    because the boundary ports correspond to the ports facing outward on the input,
    and such ports are wired to ports facing the same direction on the output."

    this makes more sense inside of a trace, where we have the concept of trace polarity
    and then input nodes of an interaction will be considered of negative polarity,
    and their ports will have flipped polarities. in that sense, the boundary ports
    are not connecting to ports of same trace polarity, but of opposite ones
  -/
  i: (BoundNeg ⊕ OutPos) ≃ (BoundPos ⊕ OutNeg)

structure TraceSetting (α β : Type) (ctx: NodeContext α) where
  /-- a finite set of labels for rule names that could appear on the trace -/
  rule_names: Finset β
  /-- a mapping that gets an interaction rule by its name in the setting -/
  rules: rule_names → InteractionRule ctx

/--
  positive nodes come from:
    1. starting net nodes
    2. output nodes from interaction steps
-/
def PosNodes
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (net_start: InteractionNet ctx)
  (num_steps: ℕ)
  (steps: Fin num_steps → ts.rule_names)
  (t: ctx.node_types) : Type :=
    {n : net_start.nodes // net_start.assign_node_type n = t} ⊕
    (Σ s : Fin num_steps,
      {n : (ts.rules (steps s)).output_nodes // ((ts.rules (steps s)).o n) = t})

/--
  negative nodes come from:
    1. ending net nodes
    2. input nodes consumed by interaction steps
-/
def NegNodes
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (net_end: InteractionNet ctx)
  (num_steps: ℕ)
  (steps: Fin num_steps → ts.rule_names)
  (t: ctx.node_types) : Type :=
    {n : net_end.nodes // net_end.assign_node_type n = t} ⊕
    {s : Fin num_steps // (ts.rules (steps s)).pos_node_type = t} ⊕
    {s : Fin num_steps // (ts.rules (steps s)).neg_node_type = t}

/--
  (possibly-temporally-inconsistent) interaction trace

  notice the trace is not defined in the obvious (and inefficient way) as a
  list of nets, it's not even obvious this definition could amount to a trace.

  the intuition behind this definition is that interactions are linear, so instead
  of taking a snapshot of the net at each step of the trace, and connecting all of
  that together, we can have a more sparse definition: every node is produced and
  consumed exactly once, so we can omit all the nodes/ports that don't get consumed
  in a step, and just have a mapping between all nodes produced (positive) to all
  nodes consumed (negative) of the same type!

  then the only thing that's missing is a way to wire the nodes/ports produced by an
  interaction to the hole that interaction left in the net (boundary ports), which
  is given by the internal wirings of every step's interaction.
-/
structure InteractionTrace (ctx: NodeContext α) (ts: TraceSetting α β ctx) where
  /-- input interaction net of the trace's first step -/
  net_start: InteractionNet ctx
  /-- output interaction net of the trace's last step -/
  net_end: InteractionNet ctx
  /-- total amount of steps in the trace -/
  num_steps: ℕ
  /-- a mapping of a step number to its corresponding rule name -/
  steps: Fin num_steps → ts.rule_names

  /-- the node bijection for each type -/
  b: ∀ t: ctx.node_types,
    (PosNodes net_start num_steps steps t) ≃ (NegNodes net_end num_steps steps t)

/-- a node's level, used for temporal consistency -/
def node_level
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) :
  (Σ t,
    (PosNodes trace.net_start trace.num_steps trace.steps t) ⊕
    (NegNodes trace.net_end trace.num_steps trace.steps t)
  ) → ℕ -- TODO: turn this ℕ into (Fin (trace.num_steps + 1))
  | ⟨_, Sum.inl (Sum.inl _)⟩ => 0                    -- starting net
  | ⟨_, Sum.inl (Sum.inr ⟨s, _⟩)⟩ => s + 1      -- output of step s
  | ⟨_, Sum.inr (Sum.inl _)⟩ => trace.num_steps + 1  -- ending net
  | ⟨_, Sum.inr (Sum.inr (Sum.inl s))⟩ => s.val + 1  -- pos input
  | ⟨_, Sum.inr (Sum.inr (Sum.inr s))⟩ => s.val + 1  -- neg input

inductive Polarity where
  | pos : Polarity
  | neg : Polarity
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
  | Polarity.pos => Polarity.neg
  | Polarity.neg => Polarity.pos

@[simp]
lemma flip_flip_is_id (pol : Polarity) : pol.flip.flip = pol := by
  cases pol <;> rfl

def port_range
  {ctx: NodeContext α}
  (t : ctx.node_types)
  (port_pol: Polarity) : Type
  := Fin (match port_pol with
      | Polarity.pos => ctx.pos_ports t
      | Polarity.neg => ctx.neg_ports t)

/--
  a trace node is a node in a trace (duh)

  technically at each step of a trace we have a different net, but since interactions
  are linear and thus every node/port is consumed exactly once (if you account for the
  end net),
-/
structure TraceNode
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) where
  t : ctx.node_types
  node : (PosNodes trace.net_start trace.num_steps trace.steps t) ⊕
         (NegNodes trace.net_end trace.num_steps trace.steps t)

/--
  a trace port is the port of a trace node, lifted.

  it's defined so we can define trace port polarity, which is necessary
  for defining temporal consistency.
-/
structure TracePort
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) where
  trace_node : TraceNode trace
  -- port polarity in the node context
  port_pol : Polarity
  port : port_range trace_node.t port_pol

-- the level of a port is the level of its node
def port_level
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (trace_port : TracePort trace) : ℕ :=
  node_level trace ⟨trace_port.trace_node.t, trace_port.trace_node.node⟩

/--
  the polarity of a port in the trace, necessary for defining temporal consistency

  the trace polarity of a port will be equal to its node context if it's a port
  from a positive (trace) node, and its opposite if it's a port on a negative (trace) node
-/
def TracePort.trace_polarity
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (trace_port : TracePort trace) : Polarity :=
  match trace_port.trace_node.node with
  -- for ports on positive trace nodes,
  -- trace port polarity is the same as port polarity
  | Sum.inl _ => trace_port.port_pol
  -- for ports on negative trace nodes,
  -- trace port polarity is the flipped port polarity
  | Sum.inr _ => trace_port.port_pol.flip

/--
  the bijection b* defined from lifting the bijections b_t (between
  nodes of same type but opposite polarities) to ports

  intuitively b* will map a port from when its introduced
  to when it's consumed. ports and nodes that don't get consumed by an
  interaction and reach the end net on the trace, are consumed then.
-/
def b_star
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) :
  TracePort trace → TracePort trace
  | ⟨⟨t, Sum.inl n⟩, pol, port⟩ =>
      ⟨⟨t, Sum.inr (trace.b t n)⟩, pol, port⟩
  | ⟨⟨t, Sum.inr n⟩, pol, port⟩ =>
      ⟨⟨t, Sum.inl ((trace.b t).symm n)⟩, pol, port⟩

def TracePosPort
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) : Type :=
  { p : TracePort trace // p.trace_polarity = Polarity.pos }

def TraceNegPort
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) : Type :=
  { p : TracePort trace // p.trace_polarity = Polarity.neg }

-- TODO: address later
set_option linter.unusedSectionVars false
lemma b_star_flips_trace_pol
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (p : TracePort trace) :
  (b_star trace p).trace_polarity = p.trace_polarity.flip := by
  cases p with
  | mk trace_node port_pol port =>
    cases trace_node with
    | mk t node =>
      cases node <;> simp [b_star, TracePort.trace_polarity, Polarity.flip]
      cases port_pol <;> simp

lemma b_star_involutive
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (p : TracePort trace) :
  b_star trace (b_star trace p) = p := by
  cases p with
  | mk trace_node port_pol port =>
    cases trace_node with
    | mk t node =>
      cases node <;> simp [b_star]

def b_star_bij_trace_port_pols
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) :
  TracePosPort trace ≃ TraceNegPort trace where
  toFun := fun ⟨p, hp⟩ =>
    ⟨b_star trace p, by simp [b_star_flips_trace_pol, hp, Polarity.flip]⟩
  invFun := fun ⟨p, hp⟩ =>
    ⟨b_star trace p, by simp [b_star_flips_trace_pol, hp, Polarity.flip]⟩
  left_inv := by
    intro ⟨p, hp⟩
    simp [b_star_involutive]
  right_inv := by
    intro ⟨p, hp⟩
    simp [b_star_involutive]

def is_principal_port
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (p : TracePort trace) : Bool :=
  p.port.val = 0

-- Helper to get the type of a node in the starting net
def start_node_type
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (n : trace.net_start.nodes) : ctx.node_types :=
  trace.net_start.assign_node_type n

-- Helper to get the type of a node in the ending net
def end_node_type
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (n : trace.net_end.nodes) : ctx.node_types :=
  trace.net_end.assign_node_type n

def start_port_to_trace_port
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  -- TODO: this is horrible, I wish there was a neat way to refactor the Pos/NegNode types
  : ((n : trace.net_start.nodes) × Fin (ctx.pos_ports (trace.net_start.assign_node_type n))) ⊕
    ((n : trace.net_start.nodes) × Fin (ctx.neg_ports (trace.net_start.assign_node_type n)))
    → TracePort trace
  | Sum.inl ⟨n, p⟩ =>
      let t := trace.net_start.assign_node_type n
      ⟨⟨t, Sum.inl (Sum.inl ⟨n, rfl⟩)⟩, Polarity.pos, p⟩
  | Sum.inr ⟨n, p⟩ =>
      let t := trace.net_start.assign_node_type n
      ⟨⟨t, Sum.inl (Sum.inl ⟨n, rfl⟩)⟩, Polarity.neg, p⟩

def end_port_to_trace_port
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  : ((n : trace.net_end.nodes) × Fin (ctx.pos_ports (trace.net_end.assign_node_type n))) ⊕
    ((n : trace.net_end.nodes) × Fin (ctx.neg_ports (trace.net_end.assign_node_type n)))
    → TracePort trace
  | Sum.inl ⟨n, p⟩ =>
      let t := trace.net_end.assign_node_type n
      ⟨⟨t, Sum.inr (Sum.inl ⟨n, rfl⟩)⟩, Polarity.pos, p⟩
  | Sum.inr ⟨n, p⟩ =>
      let t := trace.net_end.assign_node_type n
      ⟨⟨t, Sum.inr (Sum.inl ⟨n, rfl⟩)⟩, Polarity.neg, p⟩
