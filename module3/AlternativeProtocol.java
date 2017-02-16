package protocol;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import client.Utils;
import protocol.IRDTProtocol;

public class AlternativeProtocol extends IRDTProtocol implements Runnable {
	
	// ------------------------ Static Variables ------------------------
	
	// change the following as you wish:
	static final int HEADERSIZE = 4;   // number of header bytes in each packet
	static final int DATASIZE = 128;   // max. number of user data bytes in each packet
	static final int IDSIZE = HEADERSIZE - 1;
	static final int POSITIONSIZE = 1;
	static final int STREAMSIZE = 1;
	static final int TIMEOUT = 3;
	
	// ------------------------ Instance Variables ------------------------
	
	// Sender
	private Lock lock = new ReentrantLock();
	private Condition condition = lock.newCondition();
	private ArrayList<Packet> packets = new ArrayList<Packet>();
	
	// Receiver
	private int numberOfPackets = -1;
	
	// Both
	private Set<Integer> receivedIds = new HashSet<Integer>();
	
	@Override
	public void TimeoutElapsed(Object tag) {
		int z=(Integer)tag;
		// handle expiration of the timeout:
		System.out.println("Timer expired with tag="+z);
	} 
	
	// ------------------------ Sender Mode ------------------------
	
	@Override
	public void sender() {
		System.out.println("Sending...");
		(new Thread(this)).start();
		
		// Cut file into different packets
		preparePackets();
		
		// check if there are still packets to send
		while (packets.size() > 0) {
			// send packets
			sendPackets();
			
			// wait timeout
			lock.lock();
			try {
				condition.await(TIMEOUT, TimeUnit.SECONDS);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			lock.unlock();
			
			// remove acknowledged packages
			checkPackets();
		}
	}
	
	public void preparePackets() {
		// read from the input file
		Integer[] fileContents = Utils.getFileContents(getFileID());

		// keep track of where we are in the data
		int filePointer = 0;

		while (filePointer < fileContents.length) {
			// create a new packet of appropriate size
			int packetSize = Math.min(DATASIZE, fileContents.length - filePointer);
			Integer[] packetBits = new Integer[HEADERSIZE + packetSize];

			// copy databytes from the input file into data part of the packet, i.e., after the header
			System.arraycopy(fileContents, filePointer, packetBits, HEADERSIZE, packetSize);
			
			packets.add(new Packet(packetBits, packets.size()));
		}
		
	}
	
	// sends all packets from the packet list
	public void sendPackets() {
		for (Packet packet : packets) {
			getNetworkLayer().sendPacket(packet.getBytes());
		}
	}
	
	
	// removes acknowledged packages
	public void checkPackets() {
		for (Iterator<Packet> it = packets.iterator(); it.hasNext();) {
			Packet current = it.next();
			if (receivedIds.contains(current.getConvertedId())) {
				it.remove();
			}
		}
	}
	
	public void run() {
		
		// check if all packages are sent
		while (packets.size() > 0) {
			// try to fetch a packet from the network layer
			Packet packet = new Packet(getNetworkLayer().receivePacket());

			// check if we indeed received a packet
			if (packet != null) {
				
				//send ack
				receivedIds.add(packet.getConvertedId());
				
				// tell the user
				System.out.println("ACK " + packet);
			}
		}
	}
	
	// ------------------------ Receiver Mode ------------------------
	
	@Override
	public void receiver() {
		System.out.println("Receiving...");

		// loop until we are done receiving the file
		while (numberOfPackets >= 0 && receivedIds.size() == numberOfPackets) {

			// try to receive a packet from the network layer
			Packet packet = new Packet(getNetworkLayer().receivePacket());

			// if we indeed received a packet
			if (packet != null) {
				
				// send acknowledgement
				acknowledge(packet);
				
				// tell the user
				System.out.println("GOT " + packet);
				
				// add packet to the packet array at the correct position
				if (!receivedIds.contains(packet.getConvertedId())) {
					packets.add(packet.getConvertedId(), packet);
				}
			}
		}
	}
	
	// handle acknowledgements and determine number of packets
	public void acknowledge(Packet packet) {
		// if last determine number of packets
		if (packet.isLast()) {
			numberOfPackets = packet.getConvertedId();
		}
		
		// update the list of ids
		receivedIds.add(packet.getConvertedId());
		
		// send an acknowledgement
		getNetworkLayer().sendPacket(packet.getId());
	}
	
	// write the collected packets to a file
	public void orderPackets() {
		
		// create the array that will contain the file contents
		// note: we don't know yet how large the file will be, so the easiest (but not most efficient)
		//   is to reallocate the array every time we find out there's more data
		Integer[] fileContents = new Integer[0];
		
		// append the packet's data part (excluding the header) to the fileContents array, first making it larger
		for (Packet packet : packets) {
			int oldlength=fileContents.length;
			int datalen= packet.getContent().length;
			fileContents = Arrays.copyOf(fileContents, oldlength + datalen);
			System.arraycopy(packet.getBytes(), HEADERSIZE, fileContents, oldlength, datalen);
			
			// write to the output file
			Utils.setFileContents(fileContents, getFileID());
		}
	}
}