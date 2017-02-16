package protocol;

public class Packet {
	private Integer[] packet;
	private Integer[] id;
	private Integer position;
	
	
	public Packet(Integer[] packet) {
		
		this.packet = packet;
		this.position = packet[0];
		this.id = new Integer[AlternativeProtocol.IDSIZE];
		for(int i = 0; i < id.length; i++) {
			id[i] = packet[i + AlternativeProtocol.POSITIONSIZE];
		}
		//define packetId;
	}
	
	public Packet(Integer[] packet, int id) {
		
		// set packet
		this.packet = new Integer[packet.length + AlternativeProtocol.IDSIZE + AlternativeProtocol.POSITIONSIZE];
		for (int i = 0; i < packet.length; i++) {
			this.packet[i + AlternativeProtocol.POSITIONSIZE + AlternativeProtocol.IDSIZE] = packet[i];
		}
		this.position = packet[0];
		this.id = new Integer[AlternativeProtocol.IDSIZE];
		
		if(id/256 > AlternativeProtocol.IDSIZE) {
			throw new ArithmeticException("ID overflows header");
		}
		
		// set packetId;
		int index = AlternativeProtocol.POSITIONSIZE + AlternativeProtocol.IDSIZE - 1;
		int idGen = id;
		while (idGen > 255) {
			this.packet[index] = 255;
		}
		this.packet[index] = idGen;
		
		// set position
		for(int i = 0; i < this.id.length; i++) {
			this.id[i] = packet[i + AlternativeProtocol.POSITIONSIZE];
		}
		
	}
	
	public Integer[] getId() {
		return this.id;
	}
	
	public Integer getConvertedId() {
		int converted = 0;
		int shift = 1;
		for (int i : id) {
			converted += (i * shift);
			shift *= 1000;
		}
		return converted;
	}
	
	public Integer[] getBytes() {
		return this.packet;
	}
	
	public Integer[] getContent() {
		Integer[] content = new Integer[packet.length - id.length];
		for (int i = 0; i < content.length; i++) {
			content[i] = packet[i + AlternativeProtocol.HEADERSIZE];
		}
		return content;
	}
	
	public boolean isLast() {
		return position == 1;
	}
	
	public String toString() {
		return "packet => length=" + packet.length+" id="+ getConvertedId();
	}
}
