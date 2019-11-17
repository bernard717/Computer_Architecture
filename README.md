# Computer_Architecture
## 1. Milestone3
### Add new instructions to the provided single-cycle CPU, so that the 2 programs in the zip file can be executed on the new CPU.
new instructions: bne, sltu, jal, jr-ra

## 2. Milestone4
### Based on the single-cycle CPU you have designed for the milestone3, implement the pipelining with data hazard detection and handling logic.

## 3. Milestone5
### Add control hazard detection and handling logic on the pipelined CPU you have designed for the milestone4. 
* requirements
1) Branch(beq, bne) outcome and destination are calculated in the EX stage of the pipeline.
2) Jump(j, jal, jr) destination are calculated in the EX stage of the pipeline.
3) Do not implement the delayed branch.
