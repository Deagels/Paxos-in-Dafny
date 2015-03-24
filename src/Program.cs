using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using System.Numerics;
using System.Net;
using System.Net.Sockets;

namespace Paxos_Framework
{
    public static class Program
    {
        static void Main(string[] args)
        {
            Console.WriteLine("#################################### PAXOS #####################################");

            Paxos pxs = new Paxos(24805);

            string[] cmd;
            while (true)
            {
                cmd = Console.ReadLine().Split(' ');
                if (cmd.Length > 0)
                {
                    if (cmd[0] == "port")
                    {
                        if (cmd.Length == 2)
                        {
                            try { pxs.server.UpdatePort(int.Parse(cmd[1])); }
                            catch (Exception) {}
                        }
                        else if (cmd.Length == 1)
                        { pxs.server.AnnounceHost(); }
                    }
                    else if (cmd[0] == "add")
                    {
                        if (cmd.Length > 1)
                        {
                            if (cmd[1] == "proposer")
                            {
                                pxs.pro = new Proposer<int>();
                                pxs.proposers.Add(pxs.localhost);
                                Console.WriteLine("Proposer role added");
                            }
                            else if (cmd[1] == "acceptor")
                            {
                                pxs.acp = new Acceptor<int>();
                                pxs.acceptors.Add(pxs.localhost);
                                Console.WriteLine("Acceptor role added");
                            }
                            else if (cmd[1] == "learner")
                            {
                                pxs.lrn = new Learner<int>();
                                pxs.learners.Add(pxs.localhost);
                                Console.WriteLine("Learner role added");
                            }
                        }
                        else if (cmd.Length == 1)
                        { pxs.server.AnnounceHost(); }
                    }
                    else if (cmd[0] == "connect" && cmd.Length == 3)
                    {
                        try {
                            var ip = IPAddress.Parse(cmd[1]);
                            var port = int.Parse(cmd[2]);
                            IPEndPoint peer = new IPEndPoint(ip, port);
                            pxs.client.Send(peer, "connect");
                        }
                        catch (FormatException) { }
                    }
                    else if (cmd[0] == "propose" && cmd.Length == 3)
                    {
                        int round = int.Parse(cmd[1]);
                        int value = int.Parse(cmd[2]);
                        pxs.pro.__ctor(round, value);
                        pxs.client.Broadcast(pxs.acceptors, "prepare "+ round +" "+ value);
                    }
                    else { Console.WriteLine("Unknown command"); }
                }
            }
        }

        public static IPAddress LocalIPAddr()
        {
            IPHostEntry host;
            host = Dns.GetHostEntry(Dns.GetHostName());
            foreach (IPAddress ip in host.AddressList)
            {
                if (ip.AddressFamily == AddressFamily.InterNetwork) { return ip; }
            }
            return IPAddress.Parse("127.0.0.1");
        }
    }

    class Paxos
    {
        public Proposer<int> pro = new Proposer<int>();
        public Acceptor<int> acp = new Acceptor<int>();
        public Learner<int>  lrn = new Learner<int>();

        public Server server;
        public Client client;

        public List<IPEndPoint> peers     = new List<IPEndPoint>();
        public List<IPEndPoint> proposers = new List<IPEndPoint>();
        public List<IPEndPoint> acceptors = new List<IPEndPoint>();
        public List<IPEndPoint> learners  = new List<IPEndPoint>();

        public IPEndPoint localhost;
        private int replicas = 1;

        public Paxos(int port)
        {
            pro.__ctor(new BigInteger(-1), 0);
            acp.__ctor(0);
            lrn.__ctor();
            BigInteger x = new BigInteger(replicas);
            int y;
            lrn.Configure(x);
            pro.Configure(x, out x, out y);
            this.server = new Server(this, port);
            this.client = new Client(this, this.server);
            localhost = new IPEndPoint(IPAddress.Loopback, server.port);
            peers.Add(localhost);
            proposers.Add(localhost);
            acceptors.Add(localhost);
            learners.Add(localhost);
        }

        internal void AddReplica(IPEndPoint sender)
        {
            peers.Add(sender);
            proposers.Add(sender);
            acceptors.Add(sender);
            learners.Add(sender);
            replicas += 1;
            Console.WriteLine("Reconfigured to include "+ replicas +" replicas.");
            BigInteger x = new BigInteger(replicas);
            int y;
            lrn.Configure(x);
            pro.Configure(x, out x, out y);
        }
    }

    class Client
    {
        Paxos  pxs;
        Server server;
        private Socket sock = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp);

        public Client(Paxos pxs, Server srv) {
            this.pxs = pxs;
            this.server = srv;
        }

        public void Send(IPEndPoint peer, string message)
        {
            byte[] send_buffer = Encoding.ASCII.GetBytes(server.port +" "+ message);
            sock.SendTo(send_buffer, peer);
        }

        public void Broadcast(List<IPEndPoint> peers, string message)
        {
            byte[] send_buffer = Encoding.ASCII.GetBytes(server.port + " " + message);
            foreach (IPEndPoint peer in peers)
            { sock.SendTo(send_buffer, peer); }
        }
    }

    class Server
    {
        public  int       port;
        private Paxos     pxs;
        private UdpClient udpListener;
        private Thread    listenThread;

        public Server(Paxos pxs, int port)
        {
            this.pxs = pxs;
            UpdatePort(port);
            this.udpListener.Client.ReceiveTimeout = 1000; //one second
            this.listenThread = new Thread(new ThreadStart(ListenForClients));
            this.listenThread.Start();
            AnnounceHost();
        }

        public void UpdatePort(int port)
        {
            bool first = true;
            bool failed = true;
            while (failed) {
                try {
                    if (this.udpListener != null) { this.udpListener.Close(); }
                    this.udpListener = new UdpClient(port);
                    this.port = port;
                    failed = false;
                } catch {
                    if (first) {
                        Console.WriteLine("Error: Could not listen at port "+ port);
                        first = false;
                    }
                    if (port < 1024) { port = 1024; }
                    else { port += 1; }
                }
            }
        }

        public void AnnounceHost()
        {
            Console.WriteLine("hosting at " + Program.LocalIPAddr().ToString()
                +" : "+ this.port);
        }

        private void ListenForClients()
        {
            IPEndPoint remote = new IPEndPoint(IPAddress.Any, 0);
            int temp = this.port;
            while (true)
            {
                try {
                    temp = this.port;
                    //blocks until receiving a message or times out
                    Byte[] receiveBytes = this.udpListener.Receive(ref remote);
                    string str = Encoding.ASCII.GetString(receiveBytes);
                    string[] msg = str.Split(' ');
                    IPAddress remoteIP = remote.Address;
                    //Console.WriteLine(remoteIP + ":" + remote.Port + ": " + str);
                    try {
                        int port = int.Parse(msg[0]);
                        IPEndPoint sender = new IPEndPoint(remoteIP, port);
                        HandleMsg(msg, sender);
                    }
                    catch (Exception e) {
                        Console.WriteLine("Error: Could not parse message");
                        Console.WriteLine(e);
                    }
                }
                catch (SocketException)
                {
                    if (temp != this.port) { AnnounceHost(); }
                }
                catch (NullReferenceException)
                {
                    System.Threading.Thread.Sleep(1000);
                }
            }
        }

        private void HandleMsg(string[] msg, IPEndPoint sender)
        {
            if (msg.Length == 2 && msg[1] == "connect")
            {
                //if we don't have this peer in our list
                if (pxs.peers.FindIndex(item => item.Equals(sender)) == -1)
                {
                    pxs.AddReplica(sender);
                    pxs.client.Send(sender, "connect");
                    Console.WriteLine("Connected to " + sender.Address + ":" + sender.Port);
                }
            }
            else if (msg.Length == 4 && msg[1] == "prepare") // Sendt to Acceptor
            {
                BigInteger round = BigInteger.Parse(msg[2]);
                int value = int.Parse(msg[3]);
                Console.WriteLine(sender +">> Prepare( round=" +
                        round + ", value=" + value +" )");

                bool ok;
                Accepted<int> acp;
                pxs.acp.Prepare(round, value, out ok, out acp);
                if (acp.round != -1) {
                    Console.WriteLine("    accepted round: " +
                            acp.round + ", value: " + acp.value);
                } else { Console.WriteLine("    accepted none yet"); }

                if (ok) {
                    pxs.client.Send(sender, "promise " + pxs.acp.GetHashCode() +
                            " " + acp.round + " " + acp.value);
                } else { Console.WriteLine("    acceptor ignored it"); }
            }
            else if (msg.Length == 5 && msg[1] == "promise") // Sendt to Proposer
            {
                BigInteger id = BigInteger.Parse(msg[2]);
                BigInteger round = BigInteger.Parse(msg[3]);
                int value = int.Parse(msg[4]);
                Console.WriteLine(sender + ">> Promise( round=" +
                        round + ", value=" + value +" )");

                BigInteger largest;
                pxs.pro.Promise(id, round, value, out largest, out value);
                Console.WriteLine("    proposer - " + largest + ":" + value);
                pxs.client.Send(sender, "accept " + largest + " " + value);
            }
            else if (msg.Length == 4 && msg[1] == "accept") // Broadcast to Acceptors
            {
                BigInteger round = BigInteger.Parse(msg[2]);
                int value = int.Parse(msg[3]);
                Console.WriteLine(sender + ">> Accept( round=" +
                        round + ", value=" + value + " )");

                bool ok;
                Accepted<int> acp;
                pxs.acp.Accept(round, value, out ok, out acp);
                if (acp != null)
                {
                    Console.WriteLine("    acceptor - " + acp.round + ":" + acp.value);
                } else if(ok) {
                    Console.WriteLine("    acceptor returned a null reference. How is that even possible!?");
                    return;
                }
                if (ok) {
                    pxs.client.Broadcast(pxs.learners, "learn " + pxs.acp.GetHashCode() +
                            " " + acp.round + " " + acp.value);
                }
                else { Console.WriteLine("    acceptor ignored it"); }
            }
            else if (msg.Length == 5 && msg[1] == "learn") // Broadcast to Learners
            {
                BigInteger id = BigInteger.Parse(msg[2]);
                BigInteger round = BigInteger.Parse(msg[3]);
                int value = int.Parse(msg[4]);
                Console.WriteLine(sender + ">> Learn( round=" +
                        round + ", value=" + value + " )");
                bool ok;
                int learned;
                pxs.lrn.Learn(id, round, value, out ok, out learned);
                if (ok)
                {
                    Console.WriteLine("    learner - " + round + ":" + learned);
                }
                else { Console.WriteLine("    learner waits"); }
            }
            else { Console.WriteLine("Error: Unknown message format"); }
        }
    }
}
